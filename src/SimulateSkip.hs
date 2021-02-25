module SimulateSkip where

import Relude hiding (mapMaybe, filter)
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))
import Data.List (maximumBy)
import Data.Map.Strict (assocs)
import Data.Witherable

import Util
import Config
import Turing
import Tape
import ExpTape
import Skip
import Count
import HaltProof
import Results
import Glue

data PartialStepResult a = Unknown Edge
                         | Stopped InfCount a (Skip Bit)
                         | Stepped InfCount Phase a (Skip Bit)

--the data type storing various proven skips associated with a machine
--the "Phase, s" is the Phase on start and the "s" that the point is made of
--it's a maybe because some skips have a var under the point
type SkipBook s = Map (Phase, Maybe s) (Set (Skip s))

data SimState = SimState
  { _s_phase :: Phase
  , _s_tape :: ExpTape Bit InfCount
  , _s_book :: SkipBook Bit
  , _s_steps :: Steps
  }
--the count is the number of atomic steps the skip results in
data SkipResult s c = Skipped
  { _hopsTaken :: InfCount
  , _newPhase :: Phase
  , _newTape :: (ExpTape s c)
  } deriving (Eq, Ord, Show, Generic)

$(makeLenses ''SkipResult)
$(makeLenses ''SimState)

initExpTape :: s -> ExpTape s InfCount
initExpTape s = ExpTape [(s, Infinity)] (s, One) [(s, Infinity)]

dispSkipResult :: SkipResult Bit InfCount -> Text
dispSkipResult (Skipped c p tape)
  = "skipped to phase: " <> dispPhase p
  <> " and tape " <> dispExpTape tape
  <> " in " <> dispInfCount c <> " hops"

--returns nothing if the skip is inapplicable, else returns a new tape
--the fact that the type is bit is only used when running off the tape, but for now I don't want to
--generalize that out (also ExpTape would have to be generalized)
applySkip :: forall s. (Eq s) => Skip s -> (Phase, ExpTape s InfCount)
  -> Maybe (SkipResult s InfCount)
--Skip Bit -> (Phase, ExpTape Bit InfCount) -> Maybe (SkipResult Bit InfCount)
applySkip (Skip s e hopCount _) (p, tape)
  = guard (s^.cstate == p) >> packageResult <$> runEquations (matchConfigTape s tape)
  where
    packageResult :: (Map BoundVar InfCount, Map TapeVar s, ([(s, InfCount)], [(s, InfCount)]))
      -> SkipResult s InfCount
    packageResult (boundVs, tapeVs, (newLs, newRs)) = Skipped
      (updateCount boundVs hopCount)
      (e^.cstate)
      $ glomPoint $ ExpTape
          ((invariantifyList $ updateList boundVs tapeVs $ NotInfinity <$$> e^.ls) `etApp` newLs)
          (updatePoint boundVs tapeVs $ e ^. c_point)
          ((invariantifyList $ updateList boundVs tapeVs $ NotInfinity <$$> e^.rs) `etApp` newRs)
    updateInfCount :: Map BoundVar InfCount -> InfCount -> InfCount
    updateInfCount _m Infinity = Infinity
    updateInfCount m (NotInfinity c) = updateCount m c
    updateCount :: Map BoundVar InfCount -> Count -> InfCount
    updateCount m (Count n as (MonoidalMap xs))
      = (NotInfinity $ Count n as Empty) <> foldMap (updateVar m) (assocs xs)
    deVarOr :: Map TapeVar s -> VarOr s -> s
    deVarOr _m (NotVar s) = s
    deVarOr m (Var v) = case m^.at v of
      Just s -> s
      Nothing -> error "a tape var wasn't mapped in a skip"
    updateVar :: Map BoundVar InfCount -> (BoundVar, Sum Natural) -> InfCount
    updateVar m (x, (Sum n)) = n `nTimesCount` getVar m x
    getVar :: Map BoundVar InfCount -> BoundVar -> InfCount
    getVar m x = case m^.at x of
      Just c -> c
      Nothing -> error "a bound var wasn't mapped in a skip"
    updatePoint :: Map BoundVar InfCount -> Map TapeVar s
      -> (VarOr s, Location Count) -> (s, Location InfCount)
    updatePoint bs ts = (_2. _Side . _1 %~ updateCount bs) . (_1 %~ deVarOr ts)
    updateList :: Map BoundVar InfCount -> Map TapeVar s
      -> [(VarOr s, InfCount)] -> [(s, InfCount)]
    updateList bs ts = fmap $ bimap (deVarOr ts) (updateInfCount bs)

--we want to be able to apply a skip of counts to an ExpTape _ Count but also a
--skip of counts to an ExpTape _ Nat

--the skip that results from the atomic transition given an edge leading to a
--transition of the specified Phase, Bit, Dir
oneStepSkip :: Edge -> Phase -> Bit -> Dir -> Skip Bit
oneStepSkip (p, b) q c L = Skip
  (Config p [(Var (TapeVar 0), finiteCount 1)] (NotVar b, One) [])
  (Config q [] (Var (TapeVar 0), One) [(NotVar c, finiteCount 1)])
  (finiteCount 1)
  False
oneStepSkip (p, b) q c R = Skip
  (Config p [] (NotVar b, One) [(Var (TapeVar 0), finiteCount 1)])
  (Config q [(NotVar c, finiteCount 1)] (Var (TapeVar 0), One) [])
  (finiteCount 1)
  False

--the skip that results from an atomic transition which transitions a phase to itself
--writing the given bit and dir
infiniteSkip :: Edge -> Bit -> Dir -> Skip Bit
infiniteSkip (p, b) c L = Skip
  (Config p [(Var (TapeVar 0), finiteCount 1)] (NotVar b, Side (newBoundVar 0) R) [])
  (Config p [] (Var (TapeVar 0), One) [(NotVar c, newBoundVar 0)])
  (newBoundVar 0)
  False
infiniteSkip (p, b) c R = Skip
  (Config p [] (NotVar b, Side (newBoundVar 0) L) [(Var (TapeVar 0), finiteCount 1)])
  (Config p [(NotVar c, newBoundVar 0)] (Var (TapeVar 0), One) [])
  (newBoundVar 0)
  False

initTransSkip :: Edge -> Trans -> Set (Skip Bit)
--we need to modify this skip so that it's halt question is true
initTransSkip e@(p, _b) Halt = one $ oneStepSkip e p True R & halts .~ True
initTransSkip e@(p, _b) (Step q c d) | p == q = fromList
  [ oneStepSkip e q c d
  , infiniteSkip e c d
  ]
initTransSkip e (Step q c d) = one $ oneStepSkip e q c d

addSkipToBook :: (Ord s) => Skip s -> SkipBook s -> SkipBook s
addSkipToBook skip = atE (skip^.start.cstate, skip^?start.c_point._1._NotVar)
  . contains skip .~ True

initBook :: Turing -> SkipBook Bit
initBook (Turing _n trans) = appEndo (foldMap (Endo . addSkipToBook) skips) $ Empty where
  skips = foldMap (uncurry initTransSkip) $ assocs trans

lookupSkips :: (Ord s) => (Phase, s) -> SkipBook s -> Set (Skip s)
lookupSkips (p, s) book = book ^. atE (p, Just s) <> book ^. atE (p, Nothing)

--if the machine halts, pick that one, else pick the one that goes farther
skipFarthest :: (Eq s, Eq c)
  => (Skip s, SkipResult s c)
  -> (Skip s, SkipResult s c)
  -> Ordering
skipFarthest a b | a == b = EQ
skipFarthest (Skip _ _ _ True, _)   _ = LT
skipFarthest _   (Skip _ _ _ True, _) = GT
skipFarthest (_, Skipped c _ _) (_, Skipped c' _ _) = compare c c'

--simulates one step of a TM using a skip-book
--right now you can't generalize this Bit to an s because you want to be able to case
--on whether the base transition is present in the line marked **
--but that should be generalizeable
--a TapeSymbol has a function (s, Location c) -> Bit called getPointBit or something
skipStep :: Turing -> SkipBook Bit -> Phase -> ExpTape Bit InfCount
  -> PartialStepResult (ExpTape Bit InfCount)
skipStep (Turing _ trans) book p tape@(ExpTape _ls (bit, _loc) _rs)
  = case trans ^. at (p, bit) of -- **
    Nothing -> Unknown (p,bit)
    Just _ -> let
      --just tries applying all the skips. I think this will be ok, but is probably
      --too expensive and should be reworked for efficiency later
      skips = lookupSkips (p, bit) book
      appliedSkips = mapMaybe (\s -> (s,) <$> applySkip s (p, tape)) $ toList skips
      --maximumBy is safe, because we already checked the machine has this transition
      --defined, which implies at least one skip will apply
      --TODO :: unless we are at the end of the tape in which caswe we crash
      (bestSkip, Skipped hops newP newT) = maximumBy skipFarthest appliedSkips
      in --trace (toString $ (mconcat $ dispSkip . fst <$> appliedSkips) <> "\n") $
      if bestSkip ^. halts then Stopped hops newT bestSkip
        else Stepped hops newP newT bestSkip

simulateWithSkips :: Int -> Turing -> Results (ExpTape Bit InfCount)
simulateWithSkips limit startMachine
  = loop (startMachine, SimState (Phase 0) (initExpTape False) (initBook startMachine) 0) [] Empty where
  loop :: (Turing, SimState) -> [(Turing, SimState)]
    -> Results (ExpTape Bit InfCount) -> Results (ExpTape Bit InfCount)
  loop (t, (SimState p tape _book steps@((>= limit) -> True))) todos rs =
    recurse todos $ addResult t (Continue steps p tape) rs
  loop (t, (SimState p tape book steps)) todos rs = case skipStep t book p tape of
    Unknown e -> recurse ((toList $ newState <$> branchOnEdge e t) <> todos) rs where
      --we need to add the new skips to the TM's book
      newState :: Turing -> (Turing, SimState)
      newState t = (t, SimState p tape (updateBook t book) steps)
      updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
      updateBook (Turing _ trans) book = let newSkips = initTransSkip e (trans ^?! at e . _Just) in
        foldr addSkipToBook book newSkips
    Stopped c newTape _ -> recurse todos $ addResult t (Halted (steps + infCountToInt c)
      newTape) rs
    Stepped c newP newTape skip -> if c == Infinity
        then recurse todos $ addResult t (ContinueForever (SkippedToInfinity steps skip)) rs
        else loop (t, SimState newP newTape book (steps + infCountToInt c))
          todos rs

  recurse [] result = result
  recurse (x : xs) result = loop x xs result

simulateOneMachine :: Int -> Turing -> SimResult (ExpTape Bit InfCount)
simulateOneMachine limit machine
  = loop machine $ SimState (Phase 0) (initExpTape False) (initBook machine) 0 where
  loop :: Turing -> SimState -> SimResult (ExpTape Bit InfCount)
  loop _t (SimState p tape _book steps@((>= limit) -> True)) = Continue steps p tape
  loop t (SimState p tape book steps) = case skipStep t book p tape of
    Unknown _e -> Continue steps p tape
    Stopped c newTape _ -> Halted (steps + infCountToInt c)
      newTape
    Stepped c newP newTape skip -> if c == Infinity
      then ContinueForever $ SkippedToInfinity steps skip
      else loop t $ SimState newP newTape book (steps + infCountToInt c)

module SimulateSkip where

import Relude hiding (mapMaybe, filter)
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))
import Data.List (maximumBy)
import Data.Map.Strict (assocs, keysSet, unions)
import Witherable
import Prettyprinter 

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

data SkipOrigin s = Initial --from an atomic transition of the machine 
                  | Glued (Skip s) (Skip s) --from gluing together the two skips in question in order
                  | Induction (SkipBook s) Int --from stepping forward the given number of times, with the given skipbook
                  deriving (Eq, Ord, Show, Generic)

--the data type storing various proven skips associated with a machine
--the "Phase, s" is the Phase on start and the "s" that the point is made of
type SkipBook s = Map (Phase,  s) (Map (Skip s) (SkipOrigin s))

data SimState = SimState
  { _s_phase :: Phase
  , _s_tape :: ExpTape Bit InfCount
  , _s_book :: SkipBook Bit
  , _s_steps :: Steps
  , _s_trace :: [Skip Bit] -- a list of the skips used so far in order
  }

instance (Pretty s) => Pretty (SkipOrigin s) where 
  pretty Initial = "an initial skip"
  pretty (Glued first second) = "a skip resulting from gluing" <> line <> pretty first <> line 
    <> "along with" <> pretty second

--the count is the number of atomic steps the skip results in
data SkipResult s c = Skipped
  { _hopsTaken :: InfCount
  , _newPhase :: Phase
  , _newTape :: ExpTape s c
  } deriving (Eq, Ord, Show, Generic)

$(makeLenses ''SkipResult)
$(makeLenses ''SimState)

initExpTape :: s -> ExpTape s InfCount
initExpTape s = ExpTape [(s, Infinity)] s [(s, Infinity)]

dispSkipResult :: SkipResult Bit InfCount -> Text
dispSkipResult (Skipped c p tape)
  = "skipped to phase: " <> dispPhase p
  <> " and tape " <> dispExpTape tape
  <> " in " <> dispInfCount c <> " hops"

instance (Ord s, Pretty s) => Pretty (SkipBook s) where 
  pretty book = let skipPile = unions book in 
    foldMap (\(s, o) -> "the skip:" <> line <> pretty s <> line 
            <> "which resulted from" <> line <> pretty o <> line <> line) 
              $ assocs skipPile

--returns nothing if the skip is inapplicable, else returns a new tape
applySkip :: forall s. (Pretty s, Eq s) => Skip s -> (Phase, ExpTape s InfCount)
  -> Maybe (SkipResult s InfCount)
applySkip skip@(Skip s _ _ _) (p, tape)
  = guard (s^.cstate == p) >> either (const Nothing) Just
      (packageResult skip <$> runEquations (matchConfigTape s tape))

packageResult :: forall s. (Pretty s, Eq s) => Skip s -> (Map BoundVar InfCount, ([(s, InfCount)], [(s, InfCount)]))
  -> SkipResult s InfCount
packageResult (Skip _ e hopCount _) (boundVs, (newLs, newRs)) = Skipped
  (updateCount boundVs hopCount)
  (getSkipEndPhase e)
  $ getFinalET e (newLs, newRs)
  where
    getFinalET :: SkipEnd s -> ([(s, InfCount)], [(s, InfCount)]) -> ExpTape s InfCount
    getFinalET (EndMiddle c) (remLs, remRs) = ExpTape
      (finalizeList (c^.ls) `etApp` remLs)
      (c ^. c_point)
      (finalizeList (c^.rs) `etApp` remRs)
    getFinalET (EndSide _ L newRs) (remLs, remRs) = case getNewPoint remLs of
      Nothing -> error "getting new point failed, what?"
      Just (point, remremLs) -> ExpTape remremLs point (finalizeList newRs `etApp` remRs)
    getFinalET (EndSide _ R newLs) (remLs, remRs) = case getNewPoint remRs of
      Nothing -> error "getting new point failed, what?"
      Just (point, remremRs) -> ExpTape (finalizeList newLs `etApp` remLs) point remremRs

    -- updatePoint :: Map BoundVar InfCount -> (s, Location Count) -> (s, Location InfCount)
    -- updatePoint bs = (_2. _Side . _1 %~ updateCount bs)
    updateList :: Map BoundVar InfCount -> [(s, InfCount)] -> [(s, InfCount)]
    updateList bs = fmap $ fmap (updateInfCount bs)
    finalizeList :: [(s, Count)] -> [(s, InfCount)]
    finalizeList = invariantifyList . updateList boundVs . fmap (fmap NotInfinity)
    updateInfCount :: Map BoundVar InfCount -> InfCount -> InfCount
    updateInfCount _m Infinity = Infinity
    updateInfCount m (NotInfinity c) = updateCount m c
    updateCount :: Map BoundVar InfCount -> Count -> InfCount
    updateCount m (Count n as (MonoidalMap xs))
      = NotInfinity (Count n as Empty) <> foldMap (updateVar m) (assocs xs) where
      updateVar :: Map BoundVar InfCount -> (BoundVar, Sum Natural) -> InfCount
      updateVar m (x, Sum n) = n `nTimes` getVar m x
      getVar :: Map BoundVar InfCount -> BoundVar -> InfCount
      getVar m x = case m^.at x of
        Just c -> c
        Nothing -> error $ show m <> "\n" <> show x 
          <> " a bound var wasn't mapped"
--we want to be able to apply a skip of counts to an ExpTape _ Count but also a
--skip of counts to an ExpTape _ Nat

--the skip that results from the atomic transition given an edge leading to a
--transition of the specified Phase, Bit, Dir
oneStepSkip :: Edge -> Phase -> Bit -> Dir -> Skip Bit
oneStepSkip (p, b) q c d = Skip
  (Config p [] b [])
  (EndSide q d [(c, finiteCount 1)])
  (finiteCount 1)
  False

--the skip that results from an atomic transition which transitions a phase to itself
--writing the given bit and dir
infiniteSkip :: Edge -> Bit -> Dir -> Skip Bit
infiniteSkip (p, b) c L = Skip
  -- (Config p [] (b, Side (newBoundVar 0) R) [])
  (Config p [(b, newBoundVar 0)] b [])
  -- the plus one is because there is x bits to our left plus one we are pointed to 
  (EndSide p L [(c, One <> newBoundVar 0)]) 
  (One <> newBoundVar 0)
  False
infiniteSkip (p, b) c R = Skip
  -- (Config p [] (b, Side (newBoundVar 0) L) [])
  (Config p [] b [(b, newBoundVar 0)])
  (EndSide p R [(c, One <> newBoundVar 0)]) 
  (One <> newBoundVar 0)
  False

initTransSkip :: Edge -> Trans -> Set (Skip Bit)
--we need to modify this skip so that it's halt question is true
initTransSkip e@(p, _b) Halt = one $ oneStepSkip e p True L & halts .~ True
initTransSkip e@(p, _b) (Step q c d) | p == q = fromList
  [ oneStepSkip e q c d
  , infiniteSkip e c d
  ]
initTransSkip e (Step q c d) = one $ oneStepSkip e q c d

addSkipToBook :: (Ord s) => Skip s -> SkipOrigin s -> SkipBook s -> SkipBook s
addSkipToBook skip origin = atE (skip^.start.cstate, skip^.start.c_point)
  . at skip ?~ origin

addInitialSkipToBook :: (Ord s) => Skip s -> SkipBook s -> SkipBook s 
addInitialSkipToBook skip = addSkipToBook skip Initial 

initBook :: Turing -> SkipBook Bit
initBook (Turing _n trans) = appEndo (foldMap (Endo . addInitialSkipToBook) skips) Empty where
  skips = foldMap (uncurry initTransSkip) $ assocs trans

lookupSkips :: (Ord s) => (Phase, s) -> SkipBook s -> Set (Skip s)
lookupSkips (p, s) book = keysSet $ book ^. atE (p, s)

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
--or laterphina says the Skipbook maybe should be parameterized by s as well
skipStep :: Turing -> SkipBook Bit -> Phase -> ExpTape Bit InfCount
  -> PartialStepResult (ExpTape Bit InfCount)
skipStep (Turing _ trans) book p tape@(ExpTape _ls bit _rs)
  = case trans ^. at (p, bit) of -- **
    Nothing -> Unknown (p,bit)
    Just _ -> let
      --just tries applying all the skips. I think this will be ok, but is probably
      --too expensive and should be reworked for efficiency later
      skips = lookupSkips (p, bit) book
      appliedSkips = mapMaybe (\s -> (s,) <$> applySkip s (p, tape)) $ toList skips
      --maximumBy is safe, because we already checked the machine has this transition
      --defined, which implies at least one skip will apply
      --TODO :: unless we are at the end of the tape in which case we crash
      (bestSkip, Skipped hops newP newT) = maximumBy skipFarthest appliedSkips
      in --trace (toString $ (mconcat $ dispSkip . fst <$> appliedSkips) <> "\n") $
      if bestSkip ^. halts then Stopped hops newT bestSkip
        else Stepped hops newP newT bestSkip
type SkipTape = ExpTape Bit InfCount

initSkipState :: Turing -> SimState 
initSkipState t = SimState (Phase 0) (initExpTape False) (initBook t) 0 []

simulateOuterLoop :: (SimState -> SimState) -> Int -> Turing -> Results SkipTape
simulateOuterLoop updateFunc limit startMachine = undefined 

simulateOneMachine :: Int -> Turing -> SimState
  -> ([Skip Bit], Either Edge (SimResult SkipTape))
simulateOneMachine limit t = \case 
  SimState p tape _book steps@((>= limit) -> True) trace -> (trace, Right $ Continue steps p tape)
  SimState p tape book steps trace -> case skipStep t book p tape of 
    Unknown e -> (trace, Left e)
    Stopped c newTape skip -> (skip : trace, Right $ Halted (steps + infCountToInt c) newTape)
    Stepped c newP newTape skip -> case c of 
      Infinity -> (skip : trace, Right $ ContinueForever (SkippedToInfinity steps skip))
      c -> simulateOneMachine limit t $ SimState newP newTape book (steps + infCountToInt c) (skip : trace)


--TODO: known bug: we currently output a number higher than we should for step count
simulateWithSkips :: Int -> Turing -> Results SkipTape
simulateWithSkips limit startMachine
  = loop (startMachine, initSkipState startMachine) [] Empty where
  loop :: (Turing, SimState) -> [(Turing, SimState)]
    -> Results (ExpTape Bit InfCount) -> Results (ExpTape Bit InfCount)
  loop (t, s@(SimState p tape book steps trace)) todoList !rs = case simulateOneMachine limit t s of 
    (_trace, Right result) -> recurse todoList $ addResult t result rs
    (_trace, Left e) -> recurse ((newState <$> branchOnEdge e t) <> todoList) rs where
      --we need to add the new skips to the TM's book
      newState :: Turing -> (Turing, SimState)
      newState t = (t, SimState p tape (updateBook t book) steps trace)
      updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
      updateBook (Turing _ trans) book = 
        let newSkips = initTransSkip e (trans ^?! ix e) in
          foldr addInitialSkipToBook book newSkips
  recurse [] result = result
  recurse (x : xs) result = loop x xs result

simulateOneTotalMachine :: Int -> Turing -> ([Skip Bit], SimResult (ExpTape Bit InfCount))
simulateOneTotalMachine limit machine
  = loop machine $ SimState (Phase 0) (initExpTape False) (initBook machine) 0 [] where
  loop :: Turing -> SimState -> ([Skip Bit], SimResult (ExpTape Bit InfCount))
  loop _t (SimState p tape _book steps@((>= limit) -> True) trace) = (trace, Continue steps p tape)
  loop t (SimState p tape book steps trace) = case skipStep t book p tape of
    Unknown _e -> (trace, Continue steps p tape)
    Stopped c newTape _ -> (trace, Halted (steps + infCountToInt c) newTape)
    Stepped c newP newTape skip -> if c == Infinity
      then (skip : trace, ContinueForever $ SkippedToInfinity steps skip)
      else loop t $ SimState newP newTape book (steps + infCountToInt c) (skip : trace)



simulateOneMachineByGluing :: Int -> Turing -> SimState
  -> ([Skip Bit], SkipBook Bit, Either Edge (SimResult SkipTape))
simulateOneMachineByGluing limit t = \case 
  SimState p tape book steps@((>= limit) -> True) trace -> (trace, book, Right $ Continue steps p tape)
  SimState p tape book steps trace -> case skipStep t book p tape of
    Unknown e -> (trace, book, Left e)
    Stopped c newTape skip -> (skip : trace, book, Right $ Halted (steps + infCountToInt c) newTape)
    Stepped c newP newTape skip -> case c of 
      Infinity -> (skip : trace, book, Right $ ContinueForever (SkippedToInfinity steps skip)) 
      c -> simulateOneMachineByGluing limit t 
              $ SimState newP newTape newBook (steps + infCountToInt c) (skip : trace) where 
        newBook = case trace of 
          [] -> book 
          prevSkip : _rest -> case glueSkips prevSkip skip of 
            Left err -> error $ "used two skips in a row but couldn't glue:\n" 
              <> "reason: " <> err <> "\n" <> show (pretty prevSkip) 
              <> "\nsecond skip\n" <> show (pretty skip)
            Right gluedSkip -> addSkipToBook gluedSkip (Glued prevSkip skip) book 

simulateByGluing :: Int -> Turing -> Results (ExpTape Bit InfCount)
simulateByGluing limit startMachine 
 = loop (startMachine, initSkipState startMachine) [] Empty  where 
  loop :: (Turing, SimState) -> [(Turing, SimState)] -> Results SkipTape -> Results SkipTape
  loop (t, s@(SimState p tape book steps trace)) todoList rs = case simulateOneMachineByGluing limit t s of 
    (_trace, _book, Right result) -> recurse todoList $ addResult t result rs 
    (_trace, _book, Left e) -> recurse ((newState <$> branchOnEdge e t) <> todoList) rs where
      --we need to add the new skips to the TM's book
      newState :: Turing -> (Turing, SimState)
      newState t = (t, SimState p tape (updateBook t book) steps trace)
      updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
      updateBook (Turing _ trans) book = 
        let newSkips = initTransSkip e (trans ^?! ix e) in
          foldr addInitialSkipToBook book newSkips
  recurse [] result = result
  recurse (x : xs) result = loop x xs result

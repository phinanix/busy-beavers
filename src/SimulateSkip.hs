module SimulateSkip where

import Relude hiding (mapMaybe, filter, (??))
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))
import Data.List (maximumBy, foldl1)
import qualified Data.List.NonEmpty as NE ((<|))
import Data.Map.Strict (assocs, keysSet, unions)
import Witherable
import Prettyprinter

import Util
import Turing

import ExpTape
import Skip
import Count
import HaltProof
import Results
import Glue
import Simulate (initSimState)
import Control.Exception
import Safe.Partial


data PartialStepResult a = Unknown Edge
                         | Stopped InfCount a (Skip Count Bit) (Displacement InfCount)
                         | Stepped InfCount Phase a (Skip Count Bit) (Displacement InfCount)
                         | MachineStuck 
                         deriving (Eq, Ord, Show, Generic)

data SkipOrigin s = Initial --from an atomic transition of the machine 
                  | Glued (Skip Count s) (Skip Count s) --from gluing together the two skips in question in order
                  | GlueStepRange Steps Steps --gluing together all skips used in a given range of steps
                  | Induction (SkipBook s) Int --from stepping forward the given number of times, with the given skipbook
                  | InductionHypothesis 
                  deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (SkipOrigin s)

--the data type storing various proven skips associated with a machine
--the "Phase, s" is the Phase on start and the "s" that the point is made of
type SkipBook s = Map (Phase,  s) (Map (Skip Count s) (SkipOrigin s))

--which of these newtypes your history is tracks whether the history is forwards (element 0 is the first thing that happend)
--or reverse (element 0 is the most recent thing that happened)
newtype TapeHist s c = TapeHist {_tapeHist :: [(Phase, ExpTape s c)]} deriving (Eq, Ord, Show, Generic, Functor)
newtype ReverseTapeHist s c = ReverseTapeHist {_reverseTapeHist :: [(Phase, ExpTape s c)]} deriving (Eq, Ord, Show, Generic, Functor)
newtype DispHist = DispHist {_dispHist :: [Int]} deriving (Eq, Ord, Show, Generic)
newtype ReverseDispHist = ReverseDispHist {_reverseDispHist :: [Int]} deriving (Eq, Ord, Show, Generic)

instance (NFData s, NFData c) => NFData (TapeHist s c)
instance (NFData s, NFData c) => NFData (ReverseTapeHist s c)
instance NFData DispHist
instance NFData ReverseDispHist

instance Bifunctor TapeHist where 
  bimap = bimapDefault 
  
instance Bifoldable TapeHist where 
  bifoldMap = bifoldMapDefault

instance Bitraversable TapeHist where 
  bitraverse :: forall a b c d f. (Applicative f) => (a -> f c) -> (b -> f d) -> TapeHist a b -> f (TapeHist c d)
  bitraverse f g (TapeHist hist) = TapeHist <$> go where 
    go :: f [(Phase, ExpTape c d)]
    go = traverse (traverse (bitraverse f g)) hist

getTapeHist :: TapeHist s c -> [(Phase, ExpTape s c)]
getTapeHist = _tapeHist 

getReverseTapeHist :: ReverseTapeHist s c -> [(Phase, ExpTape s c)]
getReverseTapeHist = _reverseTapeHist

getDispHist :: DispHist -> [Int]
getDispHist = _dispHist
getReverseDispHist :: ReverseDispHist -> [Int]
getReverseDispHist = _reverseDispHist

data SimState = SimState
  { _s_phase :: Phase
  , _s_tape :: ExpTape Bit InfCount
  , _s_book :: SkipBook Bit
  , _s_steps :: Steps --the number of "small" / machine steps we have simulated. 
  -- a list of the skips used so far in order
  -- since it is the skips used in order, the index 0 one takes us from step 0 to step 1
  --the slice that takes you from step 5 to step 13 is index 5 to index 12 inclusive
  , _s_trace :: [Skip Count Bit]
   --a list of the (phase, tape)s seen so far in order
  , _s_reverse_history :: ReverseTapeHist Bit InfCount 
    --a map of the (phase, tape)s seen so far to the step count at which they were seen 
  , _s_history_set :: Map (Phase, ExpTape Bit InfCount) Int
  , _s_counter :: Int --the number of times we have taken a "big step". guaranteed to take on all values between 0 and n
  --the total amount of leftward (negative) or rightward (positive) displacement we have done, starting from 0
  , _s_displacement :: Int
  , _s_reverse_disp_history :: ReverseDispHist
  } deriving (Eq, Ord, Show, Generic)
instance NFData SimState

instance (Pretty s) => Pretty (SkipOrigin s) where
  pretty Initial = "an initial skip"
  pretty (Glued first second) = "a skip resulting from gluing" <> line <> pretty first <> line
    <> "along with" <> pretty second
  pretty (Induction _book _i) = "a skip proved by induction"
  pretty (GlueStepRange first second) = "a skip resulting from glueing all skips used in the step range"
    <> show first <> " to " <> show second 
  pretty InductionHypothesis = "a skip which is our current induction hypothesis"

--the count is the number of atomic steps the skip results in
data SkipResult s c = Skipped
  { _hopsTaken :: InfCount
  , _newPhase :: Phase
  , _newTape :: ExpTape s c
  , _resultingDisp :: Displacement InfCount
  } deriving (Eq, Ord, Show, Generic)

$(makeLenses ''TapeHist)
$(makeLenses ''ReverseTapeHist)
$(makeLenses ''DispHist)
$(makeLenses ''ReverseDispHist)
$(makeLenses ''SimState)
$(makeLenses ''SkipResult)

s_history :: Getter SimState (TapeHist Bit InfCount)
s_history = to $ TapeHist . reverse . getReverseTapeHist . view s_reverse_history 

s_disp_history :: Getter SimState DispHist 
s_disp_history = to $ DispHist . reverse . getReverseDispHist . view s_reverse_disp_history 

resConfig :: Lens (SkipResult s c) (SkipResult t d) (Config c s) (Config d t)
resConfig = lens get set where 
  get skipRes = etToConfig (skipRes ^. newPhase) (skipRes ^. newTape) 
  set :: SkipResult s c -> Config d t -> SkipResult t d 
  set (Skipped hops _oldPh _oldTape oldDisp) config = Skipped hops newPh newTape oldDisp where 
    (newPh, newTape) = configToET config

--TODO this can be generalized, it would need the exptape instance to be generalized too
instance Pretty (SkipResult Bit InfCount) where 
  pretty (Skipped hops phase tape disp) = "took " <> pretty hops <> " disp " <> pretty disp <> " ending in:\n" 
    <> pretty phase <> " tape: " <> pretty tape 

initExpTape :: s -> ExpTape s InfCount
initExpTape s = ExpTape [(s, Infinity)] s [(s, Infinity)]

dispSkipResult :: SkipResult Bit InfCount -> Text
dispSkipResult (Skipped c p tape disp)
  = "skipped to phase: " <> dispPhase p
  <> " and tape " <> dispExpTape tape
  <> " in " <> dispInfCount c <> " hops\ndisplacement was:" <> show disp

instance (Ord s, Pretty s) => Pretty (SkipBook s) where
  pretty book = let skipPile = unions book in
    foldMap (\(s, o) -> "the skip:" <> line <> pretty s <> line
            <> "which resulted from" <> line <> pretty o <> line <> line)
              $ assocs skipPile

--returns nothing if the skip is inapplicable, else returns a new tape
applySkip :: forall s. (Eq s, Pretty s, Partial) => Skip Count s -> (Phase, ExpTape s InfCount)
  -> Maybe (SkipResult s InfCount)
applySkip skip@(Skip s _ _ _ _) (p, tape)
  = guard (s^.cstate == p) >> either (const Nothing) Just
      (packageResult skip tape =<< runEquations (matchSkipTape skip tape))

packageResult :: forall s. (Eq s, Pretty s, Partial) => Skip Count s
  -> ExpTape s InfCount
  -> (Map BoundVar InfCount, ([(s, InfCount)], [(s, InfCount)]))
  -> Either Text (SkipResult s InfCount)
packageResult skip@(Skip _ e hopCount _ displacement) tape (boundVs, (newLs, newRs)) = (Skipped
  (updateCountToInf boundVs hopCount)
  (getSkipEndPhase e)
  <$> getFinalET e (newLs, newRs)) ??
  (simplifyInfDisplacement $ updateCountToInf boundVs <$> displacement)
  where
    getFinalET :: Partial => SkipEnd Count s -> ([(s, InfCount)], [(s, InfCount)]) -> Either Text (ExpTape s InfCount)
    getFinalET (EndMiddle c) (remLs, remRs) = let 
      ans = ExpTape
        (finalizeList (c^.ls) `etApp` remLs)
        (c ^. c_point)
        (finalizeList (c^.rs) `etApp` remRs)
      assertCond = etSatisfiesInvariant ans
      msg = "we were applying: " <> showP skip <> "\nto tape:\n" <> showP tape <> "\nresulting in:\n" <> showP ans
      in 
        (if not assertCond then trace msg else id) assert assertCond (Right ans)
      --TODO, this can fail if you are trying to prove an induction on a finite span of tape
      -- you can also hit this if you try to shift one point to the left but there is a 
      --symbolvar on the tape there 
    getFinalET (EndSide _ L newRs) (remLs, remRs) = do
      (point, remremLs) <- getNewPoint remLs
      pure $ ExpTape remremLs point (finalizeList newRs `etApp` remRs)
    getFinalET (EndSide _ R newLs) (remLs, remRs) = do
      (point, remremRs) <- getNewPoint remRs
      pure $ ExpTape (finalizeList newLs `etApp` remLs) point remremRs

    -- updatePoint :: Map BoundVar InfCount -> (s, Location Count) -> (s, Location InfCount)
    -- updatePoint bs = (_2. _Side . _1 %~ updateCount bs)
    updateList :: Map BoundVar InfCount -> [(s, InfCount)] -> [(s, InfCount)]
    updateList bs = fmap $ fmap (updateInfCount bs)
    finalizeList :: [(s, Count)] -> [(s, InfCount)]
    finalizeList = invariantifyList . updateList boundVs . fmap (fmap NotInfinity)
    updateInfCount :: Map BoundVar InfCount -> InfCount -> InfCount
    updateInfCount _m Infinity = Infinity
    updateInfCount m (NotInfinity c) = updateCountToInf m c
--we want to be able to apply a skip of counts to an ExpTape _ Count but also a
--skip of counts to an ExpTape _ Nat

--the skip that results from the atomic transition given an edge leading to a
--transition of the specified Phase, Bit, Dir
oneStepSkip :: Edge -> Phase -> Bit -> Dir -> Skip Count Bit
oneStepSkip (p, b) q c d = Skip
  (Config p [] b [])
  (EndSide q d [(c, finiteCount 1)])
  (finiteCount 1)
  False
  (OneDir d $ finiteCount 1)

--the skip that results from an atomic transition which transitions a phase to itself
--writing the given bit and dir
infiniteSkip :: Edge -> Bit -> Dir -> Skip Count Bit
infiniteSkip (p, b) c L = Skip
  -- (Config p [] (b, Side (newBoundVar 0) R) [])
  (Config p [(b, newBoundVar 0)] b [])
  -- the plus one is because there is x bits to our left plus one we are pointed to 
  (EndSide p L [(c, One <> newBoundVar 0)])
  (One <> newBoundVar 0)
  False
  (OneDir L $ One <> newBoundVar 0)
infiniteSkip (p, b) c R = Skip
  -- (Config p [] (b, Side (newBoundVar 0) L) [])
  (Config p [] b [(b, newBoundVar 0)])
  (EndSide p R [(c, One <> newBoundVar 0)])
  (One <> newBoundVar 0)
  False
  (OneDir R $ One <> newBoundVar 0)

initTransSkip :: Edge -> Trans -> Set (Skip Count Bit)
--we need to modify this skip so that it's halt question is true
--a halting machine is assumed to write True and go left
initTransSkip e@(p, _b) Halt = one $ oneStepSkip e p (Bit True) L & halts .~ True
initTransSkip e@(p, _b) (Step q c d) | p == q = fromList
  [ oneStepSkip e q c d
  , infiniteSkip e c d
  ]
initTransSkip e (Step q c d) = one $ oneStepSkip e q c d

addSkipToBook :: (Ord s) => Skip Count s -> SkipOrigin s -> SkipBook s -> SkipBook s
addSkipToBook skip origin = atE (skip^.start.cstate, skip^.start.c_point)
  . at skip ?~ origin

addInitialSkipToBook :: (Ord s) => Skip Count s -> SkipBook s -> SkipBook s
addInitialSkipToBook skip = addSkipToBook skip Initial

addMultipleToBook :: (Ord s) => [(Skip Count s, SkipOrigin s)] -> SkipBook s -> SkipBook s
addMultipleToBook xs book = foldr (uncurry addSkipToBook) book xs 

initBook :: Turing -> SkipBook Bit
initBook (Turing _n trans) = appEndo (foldMap (Endo . addInitialSkipToBook) skips) Empty where
  skips = foldMap (uncurry initTransSkip) $ assocs trans

lookupSkips :: (Ord s) => (Phase, s) -> SkipBook s -> Set (Skip Count s)
lookupSkips (p, s) book = keysSet $ book ^. atE (p, s)

--if the machine halts, pick that one, else pick the one that goes farther
skipFarthest :: (Eq s, Eq c, Eq c')
  => (Skip c s, SkipResult s c')
  -> (Skip c s, SkipResult s c')
  -> Ordering
skipFarthest a b | a == b = EQ
skipFarthest (Skip _ _ _ True _, _)   _ = LT
skipFarthest _   (Skip _ _ _ True _, _) = GT
skipFarthest (_, res1) (_, res2) = compare (res1 ^. hopsTaken) (res2 ^. hopsTaken)

--simulates one step of a TM using a skip-book
--right now you can't generalize this Bit to an s because you want to be able to case
--on whether the base transition is present in the line marked ~
--but that should be generalizeable
--a TapeSymbol has a function (s, Location c) -> Bit called getPointBit or something
--or laterphina says the Skipbook maybe should be parameterized by s as well
skipStep :: Turing -> SkipBook Bit -> Phase -> ExpTape Bit InfCount
  -> PartialStepResult (ExpTape Bit InfCount)
skipStep (Turing _ trans) book p tape@(ExpTape _ls bit _rs) = 
  case trans ^. at (p, bit) of -- ~
    Nothing -> Unknown (p,bit)
    Just _ -> let ans = pickBestSkip $ getSkipsWhichApply book p tape
      in 
        --trace ("ans was: " <> show ans)
        ans

getSkipsWhichApply :: SkipBook Bit
  -> Phase
  -> ExpTape Bit InfCount
  -> [(Skip Count Bit, SkipResult Bit InfCount)] 
getSkipsWhichApply book p tape@(ExpTape _ls bit _rs)
  = let
      --just tries applying all the skips. I think this will be ok, but is probably
      --too expensive and should be reworked for efficiency later
      skips = lookupSkips (p, bit) book
      appliedSkips = mapMaybe (\s -> (s,) <$> applySkip s (p, tape)) $ toList skips
      msg = "tape: " <> showP tape <> "\nskips which applied:\n" <> showP appliedSkips 
      in --trace msg 
        appliedSkips 

pickBestSkip :: [(Skip Count Bit, SkipResult Bit InfCount)] -> PartialStepResult (ExpTape Bit InfCount)
pickBestSkip = \case 
  [] -> MachineStuck --TODO :: can we generate this message somewhere better?
  appliedSkips -> let
    (bestSkip, Skipped hops newP newT newD) = maximumBy skipFarthest appliedSkips
    in 
      --trace ("hops: " <> showP hops <> " bestskip was:" <> showP bestSkip) $
    if bestSkip ^. halts then Stopped hops newT bestSkip newD
      else Stepped hops newP newT bestSkip newD


type SkipTape = ExpTape Bit InfCount

skipStateFromPhTape :: Turing -> Phase -> ExpTape Bit InfCount  -> SimState 
skipStateFromPhTape t ph tape = SimState ph tape (initBook t) 0 [] (ReverseTapeHist [(ph, tape)]) Empty 0 0 (ReverseDispHist [0])

initSkipState :: Turing -> SimState
initSkipState t = skipStateFromPhTape t (Phase 0) (initExpTape (Bit False))

simulateOneMachine :: Int -> Turing -> SimState
  -> ([Skip Count Bit], Either Edge (SimResult SkipTape))
simulateOneMachine limit t = \case
  --SimState p tape _book steps@((>= limit) -> True) trace _hist _ _counter -> (trace, Right $ Continue steps p tape)
  state | state ^. s_steps >= limit -> (state ^. s_trace, Right $ Continue (state ^. s_steps) (state ^. s_phase) (state ^. s_tape) (state ^. s_displacement))
  SimState p tape book steps trace hist histSet counter disp dispHist -> case skipStep t book p tape of
    MachineStuck -> error "machinestuck"
    Unknown e -> (trace, Left e)
    Stopped c newTape skip newDisp -> (skip : trace, Right $ Halted (steps + infCountToInt c) newTape (disp + dispToInt newDisp))
    Stepped c newP newTape skip newDisp -> case c of
      Infinity -> (skip : trace, Right $ ContinueForever (SkippedToInfinity steps skip))
      c -> let newHist = hist & reverseTapeHist %~ ((p, tape) :)
               newHistSet = histSet & at (p, tape) ?~ steps 
               newDispHist = dispHist & reverseDispHist %~ (disp :)
        in 
        simulateOneMachine limit t $ SimState newP newTape book (steps + infCountToInt c) (skip : trace)
           newHist newHistSet counter (disp + dispToInt newDisp) newDispHist

simulateOneTotalMachine :: Int -> Turing -> ([Skip Count Bit], SimResult (ExpTape Bit InfCount))
simulateOneTotalMachine limit machine = (^?! _Right) <$> simulateOneMachine limit machine (initSkipState machine)

updateBook :: Edge -> Turing -> SkipBook Bit -> SkipBook Bit
updateBook edge (Turing _ trans) book =
  let newSkips = initTransSkip edge (trans ^?! ix edge) in
    foldr addInitialSkipToBook book newSkips

--TODO: known bug: we currently output a number higher than we should for step count
-- simulateWithSkips :: Int -> Turing -> Results SkipTape
-- simulateWithSkips limit startMachine
--   = loop (startMachine, initSkipState startMachine) [] Empty where
--   loop :: (Turing, SimState) -> [(Turing, SimState)]
--     -> Results (ExpTape Bit InfCount) -> Results (ExpTape Bit InfCount)
--   loop (t, s@(SimState p tape book steps trace hist histSet counter)) todoList !rs = case simulateOneMachine limit t s of
--     (_trace, Right result) -> recurse todoList $ addResult t result rs
--     (_trace, Left e) -> recurse ((newState <$> branchOnEdge e t) <> todoList) rs where
--       --we need to add the new skips to the TM's book
--       newState :: Turing -> (Turing, SimState)
--       newState t = (t, SimState p tape (updateBook e t book) steps trace hist histSet counter)
--       -- updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
--       -- updateBook (Turing _ trans) book =
--       --   let newSkips = initTransSkip e (trans ^?! ix e) in
--       --     foldr addInitialSkipToBook book newSkips
--   recurse [] result = result
--   recurse (x : xs) result = loop x xs result

-- simulateOneTotalMachine :: Int -> Turing -> ([Skip Bit], SimResult (ExpTape Bit InfCount))
-- simulateOneTotalMachine limit machine
--   = loop machine $ (initSKipState machine) where
--   loop :: Turing -> SimState -> ([Skip Bit], SimResult (ExpTape Bit InfCount))
--   loop _t (SimState p tape _book steps@((>= limit) -> True) trace _hist _histSet _counter) = (trace, Continue steps p tape)
--   loop t (SimState p tape book steps trace hist histSet counter) = case skipStep t book p tape of
--     MachineStuck -> error "machinestuck"
--     Unknown _e -> (trace, Continue steps p tape)
--     Stopped c newTape _ -> (trace, Halted (steps + infCountToInt c) newTape)
--     Stepped c newP newTape skip -> if c == Infinity
--       then (skip : trace, ContinueForever $ SkippedToInfinity steps skip)
--       else loop t $ SimState newP newTape book (steps + infCountToInt c) (skip : trace) hist histSet counter



-- simulateOneMachineByGluing :: Int -> Turing -> SimState
--   -> ([Skip Bit], SkipBook Bit, Either Edge (SimResult SkipTape))
-- simulateOneMachineByGluing limit t = \case
--   SimState p tape book steps@((>= limit) -> True) trace _hist _histSet _counter -> (trace, book, Right $ Continue steps p tape)
--   SimState p tape book steps trace hist histSet counter -> case skipStep t book p tape of
--     MachineStuck -> error "machinestuck"
--     Unknown e -> (trace, book, Left e)
--     Stopped c newTape skip -> (skip : trace, book, Right $ Halted (steps + infCountToInt c) newTape)
--     Stepped c newP newTape skip -> case c of
--       Infinity -> (skip : trace, book, Right $ ContinueForever (SkippedToInfinity steps skip))
--       c -> simulateOneMachineByGluing limit t
--               $ SimState newP newTape newBook (steps + infCountToInt c) (skip : trace) hist histSet counter where
--         newBook = case trace of
--           [] -> book
--           prevSkip : _rest -> case glueSkips prevSkip skip of
--             Left err -> error $ "used two skips in a row but couldn't glue:\n"
--               <> "reason: " <> err <> "\n" <> show (pretty prevSkip)
--               <> "\nsecond skip\n" <> show (pretty skip)
--             Right gluedSkip -> addSkipToBook gluedSkip (Glued prevSkip skip) book

-- simulateByGluing :: Int -> Turing -> Results (ExpTape Bit InfCount)
-- simulateByGluing limit startMachine
--  = loop (startMachine, initSkipState startMachine) [] Empty  where
--   loop :: (Turing, SimState) -> [(Turing, SimState)] -> Results SkipTape -> Results SkipTape
--   loop (t, s@(SimState p tape book steps trace hist histSet counter)) todoList rs = case simulateOneMachineByGluing limit t s of
--     (_trace, _book, Right result) -> recurse todoList $ addResult t result rs
--     (_trace, _book, Left e) -> recurse ((newState <$> branchOnEdge e t) <> todoList) rs where
--       --we need to add the new skips to the TM's book
--       newState :: Turing -> (Turing, SimState)
--       newState t = (t, SimState p tape (updateBook t book) steps trace hist histSet counter)
--       updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
--       updateBook (Turing _ trans) book =
--         let newSkips = initTransSkip e (trans ^?! ix e) in
--           foldr addInitialSkipToBook book newSkips
--   recurse [] result = result
--   recurse (x : xs) result = loop x xs result
weird3Goal :: Skip Count Bit
weird3Goal = Skip
    -- 0 F (T, n) >T< F goes to 
    -- 0 (T, n+1) >T< F
    (Config (Phase 0) [(Bit True, newBoundVar 0), (Bit False, finiteCount 1)] (Bit True) [(Bit False, finiteCount 1)])
    (EndMiddle $ Config (Phase 0)
        [(Bit True, finiteCount 1 <> newBoundVar 0)] (Bit True) [(Bit False, finiteCount 1)])
    (finiteCount 0) --obviously this is fake for now 
    False
    Zero --obviously this is fake for now 

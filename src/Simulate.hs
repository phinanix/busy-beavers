module Simulate where

import Relude hiding (cycle, state)
import Control.Lens hiding ((<|))
import Control.Lens.Extras
import Data.List.NonEmpty ((<|))

import Beaver
import SimulateSimple (Steps, HaltProof(..))

--Pieces: turing machines with unknown edges
-- a simulator that does the usual simulate forward, while branching on unknown edges, according to
-- certain symmetry
-- a more powerful infinity prover
-- a Results type and an aggregator that adds to the results

data TMState = TMState { _phase :: Phase, _tape :: Tape} deriving (Eq, Ord, Show)

initTMState :: TMState
initTMState = TMState (Phase 0) (Tape [] False [])

data PartialStepResult = Unknown Edge | Stopped Dir Tape | Stepped Dir TMState

data SimState = SimState
  --positive
  { _stepCount :: Int
  --(stepCount `div` 2) steps after initTMState
  , _slowState :: TMState
  --stepCount steps after initTMState
  , _fastState :: TMState
  } deriving (Eq, Ord, Show)

initSimState :: SimState
initSimState = SimState 0 initTMState initTMState

data SimResult = Halted Steps Tape
               | Continue SimState
               | ContinueForever HaltProof
               deriving (Eq, Ord, Show)

simStep :: Turing -> TMState -> PartialStepResult
simStep (Turing _ trans ) (TMState p (Tape ls bit rs))
  = case trans ^. at (p, bit) of
    Nothing -> Unknown (p,bit)
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      (Stopped L $ tapeLeft $ Tape ls True rs)
    Just (Step q newBit L) ->
      (Stepped L (TMState q $ tapeLeft $ Tape ls newBit rs))
    Just (Step q newBit R) ->
      (Stepped R (TMState q $ tapeRight $ Tape ls newBit rs))

--the results should be
--  how many machines halted
--    the longest running N machines
--    the most ones N machines
--  how many ran forever, with which kind of proof
--  how many ran out of time
--  and keep a certain number thereof
data Results = Results
  { _haltCount :: Int
    , _longestRun :: Maybe (Int, Turing)
    , _mostOnes :: Maybe (Int, Turing)
  , _provenForever :: Int
    , _haltUnreachable :: Int
    , _cycle :: Int
    , _infinitySimple :: Int
    , _infinityN :: Int
  , _unproven :: Int
    , _unprovenExamples :: [(Turing, SimState)]
  } deriving (Show, Eq, Ord)

$(makeLenses ''TMState)
$(makeLenses ''SimState)
$(makeLenses ''Results)

instance AsEmpty Results where
  _Empty = only $ Results
    { _haltCount = 0
      , _longestRun = Nothing
      , _mostOnes = Nothing
    , _provenForever = 0
      , _haltUnreachable = 0
      , _cycle = 0
      , _infinitySimple = 0
      , _infinityN = 0
    , _unproven = 0
      , _unprovenExamples = []
    }
--number of unproven examples to keep
keepNum :: Int
keepNum = 20

addResult :: Turing -> SimResult -> Results -> Results
addResult turing (Halted steps tape) r =
  addHalter $ addLongest $ addOnesiest (ones tape) r where
    addLongest r = case r ^. longestRun of
      Nothing -> r & longestRun ?~ (steps, turing)
      Just (longestSteps, _) -> if steps > longestSteps
        then r & longestRun ?~ (steps, turing) else r
    addOnesiest ones r = case r ^. mostOnes of
      Nothing -> r & mostOnes ?~ (ones, turing)
      Just (mostOneCount, _) -> if ones > mostOneCount
      then r & mostOnes ?~ (ones, turing) else r
    addHalter = haltCount +~ 1
addResult _ (ContinueForever proof) r =
  r & provenForever +~ 1 & proof2lens proof +~ 1 where
    proof2lens (HaltUnreachable _) = haltUnreachable
    proof2lens (Cycle _ _) = cycle
    proof2lens (OffToInfinitySimple _ _) = infinitySimple
    proof2lens (OffToInfinityN _ _) = infinityN
addResult turing (Continue state) r = let r' = r & unproven +~ 1 in
  if r' ^. unproven > keepNum then r'
    else r' & unprovenExamples %~ ((:) (turing,state))

-- low priority todo :: filter out the machines which have duplicate states
-- creates a list of the various Turing machines that could result from filling
-- in the specified unknown edge, reducing via symmetry - if there are multiple
-- unused states, only sends us to the lowest numbered one
-- does not check that the edge is unknown, a precondition of correctness
branchOnEdge :: Edge -> Turing -> NonEmpty Turing
branchOnEdge e@(Phase newPhase, _) (Turing n m) = Turing n <$> addTrans <$> possibleTrans where
  addTrans t = m & at e ?~ t
  --if we're assigned the last unknown transition, we have to halt
  possibleTrans = if length m == 2*n - 1 then one Halt else
    --we have to use every state at least once, so when the last unused state (n-1) is
    --being assigned, or it has already been, we have to consider (not require) halting
    if used (n-2) then Halt <| continueTrans else continueTrans
  --we use nondeterminism to pick all possibilities
  continueTrans = do
    p <- validStates
    bit <- uniBit
    dir <- uniDir
    pure $ Step p bit dir
  validStates = if used (n-1)
    --all states are used, so all are valid
    then Phase <$> 0 :| [1..(n-1)]
    --some states are used, plus we can use the next unused state
    else Phase <$> (firstUnused <| usedStates)
  --this could go off the end, but is only used when the end isn't used
  firstUnused = 1 + view last1 usedStates
  --we assume 0 is used, since we don't deal with the empty machine
  --and the NonEmpty is nice
  usedStates = 0 :| filter used [1.. (n-1)]
  --a state is used if either transition is
  used i = is _Just (m ^. at (Phase i, False))
        || is _Just (m ^. at (Phase i, True))
        || i == newPhase

--the two "symmetry broken" machines that can be started with
--one only need use the "1" machine to prove the function that counts 1s, but
--either could lead to a steps champion
startMachine0 :: Int -> Turing
startMachine0 n = Turing n $ one ((Phase 0, False), (Step (Phase 1) False R))
startMachine1 :: Int -> Turing
startMachine1 n = Turing n $ one ((Phase 0, False), (Step (Phase 1) True R))

collision :: SimState -> Bool
collision (SimState steps slow fast) = steps > 0 && slow == fast

--step limit, machine to start with
simulate :: Int -> Turing -> Results
simulate limit startMachine = loop (startMachine, initSimState) [] Empty where
  -- current machine and state, next (machine&state)s, previous Results, returns updated Results
  loop :: (Turing, SimState) -> [(Turing, SimState)] -> Results -> Results
  loop (t, state@(SimState stepsTaken slow fast)) todoList rs = case simStep t fast of
    Unknown e -> recurse ((toList $ (,state) <$> branchOnEdge e t) ++ todoList) rs
    Stopped _ tape -> recurse todoList $ addResult t (Halted stepsTaken tape) rs
    Stepped _ newFast -> let
      newSlow = if (stepsTaken + 1) `div` 2 == 0  then forceAdvance t slow else slow
      newState = SimState (stepsTaken + 1) newSlow newFast
      in
      loop (t, newState) todoList rs
  forceAdvance t state = case simStep t state of
    Stepped _ newState -> newState
    _ -> error "forceAdvanced a state that doesn't advance"
  recurse [] result = result
  recurse (x : xs) result = loop x xs result

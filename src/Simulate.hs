module Simulate where

import Relude hiding (cycle, state)
import Control.Lens hiding ((<|))
import Control.Lens.Extras
import Data.List.NonEmpty ((<|))

import Util
import Turing
import Tape

--Pieces: turing machines with unknown edges
-- a simulator that does the usual simulate forward, while branching on unknown edges, according to
-- certain symmetry
-- a more powerful infinity prover
-- a Results type and an aggregator that adds to the results

data TMState = TMState { _phase :: Phase, _tape :: Tape} deriving (Eq, Ord, Show, Generic)
instance NFData TMState

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
  } deriving (Eq, Ord, Show, Generic)
instance NFData SimState

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
    , _longestRun :: Maybe (Int, Turing, Tape)
    , _mostOnes :: Maybe (Int, Turing, Tape)
  , _provenForever :: Int
    , _haltUnreachable :: Int
    , _cycledCount :: Int
    , _infinitySimple :: Int
    , _infinityN :: Int
  , _unproven :: Int
    , _unprovenExamples :: [(Turing, SimState)]
  } deriving (Show, Eq, Ord, Generic)
instance NFData Results

$(makeLenses ''TMState)
$(makeLenses ''SimState)
$(makeLenses ''Results)

mirrorTMState :: TMState -> TMState
mirrorTMState (TMState p t) = TMState p $ mirrorTape t

mirrorSimState :: SimState -> SimState
mirrorSimState (SimState steps slow fast)
  = SimState steps (mirrorTMState slow) (mirrorTMState fast)

instance AsEmpty Results where
  _Empty = only $ Results
    { _haltCount = 0
      , _longestRun = Nothing
      , _mostOnes = Nothing
    , _provenForever = 0
      , _haltUnreachable = 0
      , _cycledCount = 0
      , _infinitySimple = 0
      , _infinityN = 0
    , _unproven = 0
      , _unprovenExamples = []
    }
--number of unproven examples to keep
keepNum :: Int
keepNum = 3

addResult :: Turing -> SimResult -> Results -> Results
addResult turing (Halted steps tape) r =
  addHalter $ addLongest $ addOnesiest (ones tape) r where
    addLongest r = case r ^. longestRun of
      Nothing -> r & longestRun ?~ (steps, turing, tape)
      Just (longestSteps, _, _) -> if steps > longestSteps
        then r & longestRun ?~ (steps, turing, tape) else r
    addOnesiest ones r = case r ^. mostOnes of
      Nothing -> r & mostOnes ?~ (ones, turing, tape)
      Just (mostOneCount, _, _) -> if ones > mostOneCount
      then r & mostOnes ?~ (ones, turing, tape) else r
    addHalter = haltCount +~ 1
addResult _ (ContinueForever proof) r =
  r & provenForever +~ 1 & proof2lens proof +~ 1 where
    proof2lens (HaltUnreachable _) = haltUnreachable
    proof2lens (Cycle _ _) = cycledCount
--    proof2lens (OffToInfinitySimple _ _) = infinitySimple
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
--not valid for n=1, where the machine must halt immediately, or run forever.
startMachine0 :: Int -> Turing
startMachine0 1 = uni1Machine
startMachine0 n = Turing n $ one ((Phase 0, False), (Step (Phase 1) False R))
startMachine1 :: Int -> Turing
startMachine1 1 = uni1Machine
startMachine1 n = Turing n $ one ((Phase 0, False), (Step (Phase 1) True R))
--for n=1 if you don't halt right away, you are doomed to loop forever
uni1Machine :: Turing
uni1Machine = Turing 1 $ one ((Phase 0, False), Halt)

collision :: SimState -> Bool
collision (SimState steps slow fast) = steps > 1 && slow == fast

getSteps :: SimState -> (Steps, Steps)
getSteps (SimState steps _ _) = (steps `div` 2, steps)

--step limit, machine to start with
simulate :: Int -> Turing -> Results
simulate limit startMachine = loop (startMachine, initSimState) [] Empty where
  -- current machine and state, next (machine&state)s, previous Results, returns updated Results
  loop :: (Turing, SimState) -> [(Turing, SimState)] -> Results -> Results
  loop (t, s@(collision -> True)) todoList !rs
    = --trace "added cycle" $
      recurse todoList $ addResult t (ContinueForever $ uncurry Cycle $ getSteps s) rs
  loop (t, s@(SimState ( ((\stepsTaken -> stepsTaken > limit) -> True)) _ _)) todoList !rs =
    -- if rs ^. unprovenExamples == [] then trace (show steps <> "\n") $
    --     recurse todoList $ addResult t (Continue s) rs
    --   else
        recurse todoList $ addResult t (Continue s) rs
  loop (t, s@(SimState stepsTaken slow fast)) todoList !rs = case proveForever t s of
    Just proof -> --trace "added infinity" $
      recurse todoList $ addResult t (ContinueForever proof) rs
    Nothing -> let newStepsTaken = stepsTaken+1 in
      case simStep t fast of
        Unknown e -> --trace ("branched on " <> show e) $
          recurse ((toList $ (,s) <$> branchOnEdge e t) ++ todoList) rs
        Stopped _ tape -> recurse todoList $ addResult t (Halted newStepsTaken tape) rs
        Stepped _ newFast -> let
          newSlow = if newStepsTaken `mod` 2 == 0  then forceAdvance t slow else slow
          newState = SimState newStepsTaken newSlow newFast
          in
          loop (t, newState) todoList rs
  forceAdvance t s = case simStep t s of
    Stepped _ newState -> newState
    _ -> error "forceAdvanced a state that doesn't advance"
  recurse [] result = result
  recurse (x : xs) result = loop x xs result

proveForever :: Turing -> SimState -> Maybe HaltProof
proveForever = infiniteCycle

infiniteSimLimit :: Steps
infiniteSimLimit = 20

infiniteCycle :: Turing -> SimState -> Maybe HaltProof
infiniteCycle t s = infiniteRight t s <|> infiniteLeft t s

infiniteRight :: Turing -> SimState -> Maybe HaltProof
infiniteRight t (SimState originalSteps _ mState@(TMState startPhase (Tape startLs False [])))
  = step 0 0 0 mState where
  -- first arg counts number of steps taken in this halting proof
  -- second arg counts distance left or right from our starting point,
  -- left is negative, right is positive
  -- third arg counts max leftward distance (in positive terms)
  step :: Steps -> Int -> Int -> TMState -> Maybe HaltProof
  --we hit our step limit
  step ((\i -> i >= infiniteSimLimit) -> True) _ _ _ = Nothing
  --here, distance is negative, so we just simulate another step
  step steps dist@((\d -> d <= 0) -> True) maxL s = stepRecurse steps dist maxL s
  --here, distance is positive, so we have a chance to fulfull the conditions
  --to prove infinite rightward movement
  step steps dist maxL s@(TMState (((==) startPhase) -> True) (Tape ls False [])) =
    if take maxL ls == take maxL startLs then Just $ OffToInfinityN originalSteps R
    else stepRecurse steps dist maxL s
  step steps dist maxL s = stepRecurse steps dist maxL s
  stepRecurse steps dist maxL s = case simStep t s of
    Stepped L s' -> step (steps + 1) (dist - 1) (newMax maxL (dist - 1)) s'
    Stepped R s' -> step (steps + 1) (dist + 1) maxL s'
    _ -> Nothing
  --first arg is old max, second arg is (signed) distance
  --max can only be beaten by a negative distance, since it's the farthest left
  newMax :: Int -> Int -> Int
  newMax oldMax ((\i -> i >= 0) -> True) = oldMax
  newMax oldMax (negate -> newPosDist) = max oldMax newPosDist
infiniteRight _ _ = Nothing

infiniteLeft :: Turing -> SimState -> Maybe HaltProof
infiniteLeft t s = mirrorHaltProof <$> infiniteRight (mirrorTuring t) (mirrorSimState s)

dispTMState :: TMState -> Text
dispTMState (TMState (Phase i) tape) = "phase: " <> show i <> " tape: " <> dispTape tape

dispSimState :: SimState -> Text
dispSimState (SimState steps slow fast) = "steps: " <> showInt3Wide steps
  <> "\nslow: " <> dispTMState slow
  <> "\nfast: " <> dispTMState fast

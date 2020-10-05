module Simulate where

import Relude
import Control.Lens

import Util
import Config
import Turing
import Tape
import ExpTape
import Skip
import Count
import HaltProof
import Results

--Pieces: turing machines with unknown edges
-- a simulator that does the usual simulate forward, while branching on unknown edges, according to
-- certain symmetry
-- a more powerful infinity prover
-- a Results type and an aggregator that adds to the results

data TMState a = TMState { _phase :: Phase, _tape :: a} deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (TMState a)

initTMState :: TMState Tape
initTMState = TMState (Phase 0) (Tape [] False [])

data PartialStepResult a = Unknown Edge | Stopped Dir a | Stepped Dir (TMState a)

data SimState a = SimState
  --positive
  { _stepCount :: Int
  --(stepCount `div` 2) steps after initTMState
  , _slowState :: (TMState a)
  --stepCount steps after initTMState
  , _fastState :: (TMState a)
  } deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (SimState a)

initSimState :: SimState Tape
initSimState = SimState 0 initTMState initTMState

simStep :: Turing -> TMState Tape -> PartialStepResult Tape
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


$(makeLenses ''TMState)
$(makeLenses ''SimState)

mirrorTMState :: TMState Tape -> TMState Tape
mirrorTMState (TMState p t) = TMState p $ mirrorTape t

mirrorSimState :: SimState Tape -> SimState Tape
mirrorSimState (SimState steps slow fast)
  = SimState steps (mirrorTMState slow) (mirrorTMState fast)

collision :: Eq a => SimState a -> Bool
collision (SimState steps slow fast) = steps > 1 && slow == fast

getSteps :: SimState a -> (Steps, Steps)
getSteps (SimState steps _ _) = (steps `div` 2, steps)

--step limit, machine to start with
simulate :: Int -> Turing -> Results Tape
simulate limit startMachine = loop (startMachine, initSimState) [] Empty where
  -- current machine and state, next (machine&state)s, previous Results, returns updated Results
  loop :: (Turing, SimState Tape) -> [(Turing, SimState Tape)] -> Results Tape -> Results Tape
  loop (t, s@(collision -> True)) todoList !rs
    = recurse todoList $ addResult t (ContinueForever $ uncurry Cycle $ getSteps s) rs
  loop (t, (SimState (stepCount@((\stepsTaken -> stepsTaken > limit) -> True))
    _ (TMState p finalTape))) todoList !rs =
        recurse todoList $ addResult t (Continue stepCount p finalTape) rs
  loop (t, s@(SimState stepsTaken slow fast)) todoList !rs = case proveForever t s of
    Just proof -> recurse todoList $ addResult t (ContinueForever proof) rs
    Nothing -> let newStepsTaken = stepsTaken+1 in
      case simStep t fast of
        Unknown e -> recurse ((toList $ (,s) <$> branchOnEdge e t) ++ todoList) rs
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
  recurse ((t,s) : xs) result = case staticAnalyze t of
    Just proof -> recurse xs $ addResult t (ContinueForever proof) result
    Nothing -> loop (t,s) xs result

--halting analyses that can be performed without simulating the machine
staticAnalyze :: Turing -> Maybe HaltProof
staticAnalyze = backwardSearch
-- staticAnalyze = const Nothing

--attempting to prove the machine runs forever starting at a given state
proveForever :: Turing -> SimState Tape -> Maybe HaltProof
proveForever t s@(SimState stepsTaken _ _) = infiniteCycle (min stepsTaken infiniteSimLimit) t s

infiniteCycle :: Int -> Turing -> SimState Tape -> Maybe HaltProof
infiniteCycle limit t s = infiniteRight limit t s <|> infiniteLeft limit t s

infiniteRight :: Int -> Turing -> SimState Tape -> Maybe HaltProof
infiniteRight limit t (SimState originalSteps _ mState@(TMState startPhase (Tape startLs False [])))
  = step 0 0 0 mState where
  -- first arg counts number of steps taken in this halting proof
  -- second arg counts distance left or right from our starting point,
  -- left is negative, right is positive
  -- third arg counts max leftward distance (in positive terms)
  step :: Steps -> Int -> Int -> TMState Tape -> Maybe HaltProof
  --we hit our step limit
  step ((\i -> i >= limit) -> True) _ _ _ = Nothing
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
infiniteRight _ _ _ = Nothing

infiniteLeft :: Int -> Turing -> SimState Tape -> Maybe HaltProof
infiniteLeft limit t s = mirrorHaltProof <$> infiniteRight limit (mirrorTuring t) (mirrorSimState s)

dispTMState :: TMState Tape -> Text
dispTMState (TMState (Phase i) tape) = "phase: " <> show i <> " tape: " <> dispTape tape

dispSimState :: SimState Tape -> Text
dispSimState (SimState steps slow fast) = "steps: " <> showInt3Wide steps
  <> "\nslow: " <> dispTMState slow
  <> "\nfast: " <> dispTMState fast

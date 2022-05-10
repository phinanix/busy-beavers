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

initTMState :: TMState (Tape Bit)
initTMState = TMState (Phase 0) (Tape [] (Bit False) [])

data PartialStepResult a = Unknown Edge | Stopped Dir a | Stepped Dir (TMState a)

data SimState a = SimState
  --positive
  { _stepCount :: Int
  --(stepCount `div` 2) steps after initTMState
  , _slowState :: TMState a
  --stepCount steps after initTMState
  , _fastState :: TMState a
  } deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (SimState a)

initSimState :: SimState (Tape Bit)
initSimState = SimState 0 initTMState initTMState

simStep :: Turing -> TMState (Tape Bit) -> PartialStepResult (Tape Bit)
simStep (Turing _ trans ) (TMState p (Tape ls bit rs))
  = case trans ^. at (p, bit) of
    Nothing -> Unknown (p,bit)
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      Stopped L $ tapeLeft $ Tape ls (Bit True) rs
    Just (Step q newBit L) ->
      Stepped L (TMState q $ tapeLeft $ Tape ls newBit rs)
    Just (Step q newBit R) ->
      Stepped R (TMState q $ tapeRight $ Tape ls newBit rs)


$(makeLenses ''TMState)
$(makeLenses ''SimState)

mirrorTMState :: TMState (Tape Bit) -> TMState (Tape Bit)
mirrorTMState (TMState p t) = TMState p $ mirrorTape t

mirrorSimState :: SimState (Tape Bit) -> SimState (Tape Bit)
mirrorSimState (SimState steps slow fast)
  = SimState steps (mirrorTMState slow) (mirrorTMState fast)

collision :: Eq a => SimState a -> Bool
collision (SimState steps slow fast) = steps > 1 && slow == fast

getSteps :: SimState a -> (Steps, Steps)
getSteps (SimState steps _ _) = (steps `div` 2, steps)
{-
-- step limit, machine, current state
-- if we hit an unknown edge, we have to stop, and we return that. else we'll get to a result and return the result
simulateOneMachine :: Int -> Turing -> SimState (Tape Bit) -> Either Edge (SimResult Bit (Tape Bit))
simulateOneMachine limit t = \case
  s@(collision -> True) -> Right $ ContinueForever $ uncurry Cycle $ getSteps s
  SimState stepCount@((>= limit) -> True) _ (TMState p finalTape) -> Right $ Continue stepCount p finalTape 0
  s@(SimState stepsTaken slow fast) -> case proveForever t s of
    Just hp -> Right $ ContinueForever hp
    Nothing -> let newStepsTaken = stepsTaken + 1 in
      case simStep t fast of
        Unknown e -> Left e
        Stopped _ tape -> Right $ Halted newStepsTaken tape 0
        Stepped _ newFast -> let
          newSlow = if even newStepsTaken  then forceAdvance t slow else slow
          newState = SimState newStepsTaken newSlow newFast
          in
            simulateOneMachine limit t newState
  where
    forceAdvance t s = case simStep t s of
      Stepped _ newState -> newState
      _ -> error "forceAdvanced a state that doesn't advance"


--step limit, machine to start with
simulate :: Int -> Turing -> Results (Tape Bit)
simulate limit startMachine = loop (startMachine, initSimState) [] Empty where
  -- current machine and state, next (machine&state)s, previous Results, returns updated Results
  loop :: (Turing, SimState (Tape Bit)) -> [(Turing, SimState (Tape Bit))] -> Results (Tape Bit) -> Results (Tape Bit)
  loop (t, s) todoList !rs = case simulateOneMachine limit t s of
    Left e -> recurse (toList ((,s) <$> branchOnEdge e t) ++ todoList) rs
    Right result -> recurse todoList $ addResult t result rs
  recurse :: [(Turing, SimState (Tape Bit))] -> Results (Tape Bit) -> Results (Tape Bit)
  recurse [] result = result
  recurse ((t,s) : xs) result = case staticAnalyze t of
    Just proof -> recurse xs $ addResult t (ContinueForever proof) result
    Nothing -> loop (t,s) xs result
-}
--halting analyses that can be performed without simulating the machine
staticAnalyze :: Turing -> Maybe (HaltProof s)
staticAnalyze = backwardSearch
-- staticAnalyze = const Nothing

--attempting to prove the machine runs forever starting at a given state
proveForever :: Turing -> SimState (Tape Bit) -> Maybe (HaltProof s)
proveForever t s@(SimState stepsTaken _ _) = infiniteCycle (min stepsTaken infiniteSimLimit) t s

infiniteCycle :: Int -> Turing -> SimState (Tape Bit) -> Maybe (HaltProof s)
infiniteCycle limit t s = infiniteRight limit t s <|> infiniteLeft limit t s

infiniteRight :: forall s. Int -> Turing -> SimState (Tape Bit) -> Maybe (HaltProof s)
infiniteRight limit t (SimState originalSteps _ mState@(TMState startPhase (Tape startLs (Bit False) [])))
  = step 0 0 0 mState where
  -- first arg counts number of steps taken in this halting proof
  -- second arg counts distance left or right from our starting point,
  -- left is negative, right is positive
  -- third arg counts max leftward distance (in positive terms)
  step :: Steps -> Int -> Int -> TMState (Tape Bit) -> Maybe (HaltProof s)
  --we hit our step limit
  step ((>= limit) -> True) _ _ _ = Nothing
  --here, distance is negative, so we just simulate another step
  step steps dist@((<= 0) -> True) maxL s = stepRecurse steps dist maxL s
  --here, distance is positive, so we have a chance to fulfull the conditions
  --to prove infinite rightward movement
  step steps dist maxL s@(TMState ((startPhase ==) -> True) (Tape ls (Bit False) [])) =
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
  newMax oldMax ((>= 0) -> True) = oldMax
  newMax oldMax (negate -> newPosDist) = max oldMax newPosDist
infiniteRight _ _ _ = Nothing

infiniteLeft :: Int -> Turing -> SimState (Tape Bit) -> Maybe (HaltProof s)
infiniteLeft limit t s = mirrorHaltProof <$> infiniteRight limit (mirrorTuring t) (mirrorSimState s)

dispTMState :: TMState (Tape Bit) -> Text
dispTMState (TMState (Phase i) tape) = "phase: " <> show i <> " tape: " <> dispTape tape

dispSimState :: SimState (Tape Bit) -> Text
dispSimState (SimState steps slow fast) = "steps: " <> showInt3Wide steps
  <> "\nslow: " <> dispTMState slow
  <> "\nfast: " <> dispTMState fast

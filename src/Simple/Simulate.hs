module Simple.Simulate where
import Relude hiding (state)
import Control.Lens

import Turing
import Simple.Tape

--the type of proofs that a TM will not halt
-- - HaltUnreachable means the Halt state is never transitioned to from the current state
--   and any states it transitions to
-- - Cycle means that the state reached after a number of steps and a greater number
--   of steps is identical
-- - OffToInfinitySimple means that after the given number of steps, the machine will
--   continue off in the given direction infintitely, never changing states
-- - OffToInfinityN means that after the given number of steps, the machine will
--   continue off in the given direction infinitely, in a short loop, which is checked
--   up to a specified bound N
data HaltProof
  = HaltUnreachable Phase
  | Cycle Steps Steps
  | OffToInfinitySimple Steps Dir
  | OffToInfinityN Steps Dir
  deriving (Eq, Ord, Show, Generic)
instance NFData HaltProof

mirrorHaltProof :: HaltProof -> HaltProof
mirrorHaltProof (OffToInfinityN s d) = OffToInfinityN s $ mirrorDir d
mirrorHaltProof (OffToInfinitySimple s d) = OffToInfinitySimple s $ mirrorDir d
mirrorHaltProof h = h

--starts at a phase, maintains a list to explore, and a set of visited phases,
--returns a proof of Halt's unreachability, if available
-- Note that "first" is the very starting phase, used for the proof only
--          first      current      to explore next, seen
dfsToHalt :: Turing -> Phase -> Phase -> State ([Phase], Set Phase) (Maybe HaltProof)
dfsToHalt t@(Turing _ transitions) first current = do
  b1 <- try current False
  b2 <- try current True
  if b1 || b2
    then pure Nothing --they found halt, so we have no proof
    else do
      _2 . contains current .= True
      use _1 >>= \case
      --we won't find halt because there is no more to explore
        [] -> pure $ Just $ HaltUnreachable first
        ((!newPhase) : (!newExploreList)) -> do
          _1 .= newExploreList
          dfsToHalt t first newPhase
  where
  --returns true if it has proven halt is reachable, else false
  try :: Phase -> Bool -> State ([Phase], Set Phase) Bool
  try phase bit = case transitions ^. at (phase, bit) of
    --if the current state leads to an unknown edge, that unknown edge could
    --be assigned to halt, thus halt is reachable
    Nothing -> pure True
    --we found halt
    Just Halt -> pure True
    Just (Step phase1 _ _) -> use (_2 . contains phase1) >>= \case
      --we've already seen this state so we give up - we won't find halt here
      True -> pure False
      --we haven't seen this state so we have to add it to our frontier - we also
      -- won't find halt here
      False -> do
        _1 %= ((:) phase1)
        pure False

simpleInfiniteLeft :: SimState -> Turing -> Maybe HaltProof
--suppse we are all the way at the left side of the tape, looking at a False
simpleInfiniteLeft (phase, steps, Tape [] False _) (Turing{transitions = trans}) =
  --and when we transition from this phase and a false, we step left, and stay in the
  --same phase (doesn't matter what we write)
  case trans ^. at (phase,False) of
    --then this pattern repeats forever and we never halt
    --TODO :: this phase name overwrites the previous phase
    Just (Step (((==) phase) -> True) _ L) -> Just $ OffToInfinitySimple steps L
    --else give up
    _ -> Nothing
simpleInfiniteLeft _ _ = Nothing

--this is analagous to the other case, but mirrored
-- TODO :: refactor this to not duplicate so much code
simpleInfiniteRight :: SimState -> Turing -> Maybe HaltProof
simpleInfiniteRight simState turing = mirrorHaltProof <$>
  simpleInfiniteLeft (mirrorSimState simState) (mirrorTuring turing)

infiniteSimLimit :: Int
infiniteSimLimit = 20

infiniteCycle :: SimState -> Turing -> Maybe HaltProof
infiniteCycle s t = infiniteRight s t <|> infiniteLeft s t

--suppose the machine is at the RHS of the tape, in some phase, and after i steps
--returns to the RHS of the tape, in that phase. Further, suppose the machine traveled
--at most l steps to the left of its starting point throughout those i steps, and
--the last l entries on the tape at the start are the same as the last l entries on
--the tape after it has performed i steps
--then the machine will repeat those i steps forever, falling off the RHS of the tape
--infinitely
infiniteRight :: SimState -> Turing -> Maybe HaltProof
infiniteRight startState@(startPhase, originalSteps, Tape startLs False []) t
  = step 0 0 0 startState where
  -- first arg counts number of steps taken in this halting proof
  -- second arg counts distance left or right from our starting point,
  -- left is negative, right is positive
  -- third arg counts max leftward distance (in positive terms)
  step :: Steps -> Int -> Int -> SimState -> Maybe HaltProof
  --we hit our step limit
  step ((\i -> i >= infiniteSimLimit) -> True) _ _ _ = Nothing
  --here, distance is negative, so we just simulate another step
  step steps dist@((\d -> d <= 0) -> True) maxL s = stepRecurse steps dist maxL s
  --here, distance is positive, so we have a chance to fulfull the conditions
  --to prove infinite rightward movement
  step steps dist maxL s@(((==) startPhase) -> True, _, Tape ls False []) =
    if take maxL ls == take maxL startLs then Just $ OffToInfinityN originalSteps R
    else stepRecurse steps dist maxL s
  step steps dist maxL s = stepRecurse steps dist maxL s
  stepRecurse steps dist maxL s = case simStepWithDir t s of
    (Stepped s', L) -> step (steps + 1) (dist - 1) (newMax maxL (dist - 1)) s'
    (Stepped s', R) -> step (steps + 1) (dist + 1) maxL s'
    _ -> Nothing
  --first arg is old max, second arg is (signed) distance
  --max can only be beaten by a negative distance, since it's the farthest left
  newMax :: Int -> Int -> Int
  newMax oldMax ((\i -> i >= 0) -> True) = oldMax
  newMax oldMax (negate -> newPosDist) = max oldMax newPosDist
infiniteRight _ _ = Nothing

infiniteLeft :: SimState -> Turing -> Maybe HaltProof
infiniteLeft s t = mirrorHaltProof <$>
  infiniteRight (mirrorSimState s) (mirrorTuring t)

testHalt :: SimState -> Turing -> Maybe HaltProof
testHalt s@(phase, _, _) t
  = simpleInfiniteLeft s t
  <|> simpleInfiniteRight s t
  <|> evalState (dfsToHalt t phase phase) (Empty, Empty)
  <|> infiniteCycle s t

--the number of steps a machine has taken
type SimState = (Phase, Steps, Tape)

mirrorSimState :: SimState -> SimState
mirrorSimState = fmap mirrorTape

data TotalStepResult = Stopped Steps Tape | Stepped SimState

--Unknown means we don't know how to make progress
--from the current state, because it isn't in the transition map
--Stop means the machine halted with the given tape
--Continue means the machine hasn't halted and the current state is given
--ContinueForever means the machine has been proven to run forever
data SimResult = Halted Steps Tape
  | Continue SimState | ContinueForever HaltProof deriving (Eq, Ord, Show, Generic)

instance NFData SimResult

stepRtoSimR :: TotalStepResult -> SimResult
stepRtoSimR (Stopped steps tape) = Halted steps tape
stepRtoSimR (Stepped s) = Continue s

initState :: SimState
initState = (Phase 0, 0, Tape [] False [])

dispStartState :: SimState
dispStartState = (Phase 0, 0, Tape falses False falses) where
  falses = take 12 $ repeat False

simStepWithDir :: Turing -> SimState -> (TotalStepResult, Dir)
simStepWithDir (Turing _ trans ) (i, steps, (Tape ls bit rs))
  = case trans ^. at (i, bit) of
    Nothing -> error "Total Turing machine wasn't total"
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      (Stopped (steps + 1) $ tapeLeft $ Tape ls True rs, L)
    Just (Step j newBit L) ->
      (Stepped (j, steps + 1, tapeLeft $ Tape ls newBit rs), L)
    Just (Step j newBit R) ->
      (Stepped (j, steps + 1, tapeRight $ Tape ls newBit rs), R)

simStep :: Turing -> SimState -> TotalStepResult
simStep t s = fst $ simStepWithDir t s

--simulates a machine for the given number of steps, where the state is the number
--of steps taken so far
simulate :: Int -> SimState -> Turing -> SimResult
simulate limit state@(_, (\i -> i > limit) -> True, _) _ = Continue state
simulate limit state turing = case simStep turing state of
    result@(Stopped _ _) -> stepRtoSimR result
    (Stepped newState) -> simulate limit newState turing

--checks if the slow simulation has run into the fast simulation, which of course
--is trivially true at t=0 but we want rule that out
collision :: SimState -> SimState -> Bool
collision (p, steps, t) (p', _, t') = (p == p') && (t == t') && (steps > 0)

--simulates a machine for at most the given limit steps, working to prove it runs forever
simulateHalt :: Int -> Turing -> SimResult
simulateHalt limit t = simulateHaltHelper limit (initState, initState) t where
  --first element of tuple is smallStep, second is bigStep, advancing at twice the rate
  --if smallStep ever == bigstep, then we have found a cycle
  simulateHaltHelper :: Int -> (SimState, SimState) -> Turing -> SimResult
  simulateHaltHelper limit (_, state@(_, (\i -> i > limit) -> True, _)) _ = Continue state
  simulateHaltHelper _ states@(uncurry collision -> True) _ = let
    ((_, smallSteps, _), (_, largeSteps, _)) = states in
    ContinueForever $ Cycle smallSteps largeSteps
  simulateHaltHelper limit (littleState, bigState) t =
    --step bigState once
    case simStep t bigState of
      result@(Stopped _ _) -> stepRtoSimR result
      (Stepped bigState1) ->
        --step bigState again
        case simStep t bigState1 of
          result@(Stopped _ _) -> stepRtoSimR result
          (Stepped bigState2) -> case testHalt bigState2 t of
            Just haltProof -> ContinueForever haltProof
            --step littleState once
            Nothing -> case simStep t littleState of
              (Stepped littleState1)
                -> simulateHaltHelper limit (littleState1, bigState2) t
              _ -> error "small state didn't continue, but we already checked it does"

module HaltProof where
import Relude
import Control.Lens

import Beaver

--the type of proofs that a TM will not halt
-- - HaltUnreachable means the Halt state is never transitioned to from the current state
--   and any states it transitions to
-- - Cycle means that the state reached after a number of steps and a greater number
--   of steps is identical
data HaltProof = HaltUnreachable Phase | Cycle Steps Steps deriving (Eq, Ord, Show)


testHalt :: SimState -> Turing -> Maybe HaltProof
testHalt (phase, _, tape) (Turing stateCount transitions)
  = if evalState (dfsToHalt phase) (Empty, Empty)
    then --we can find halt!
      Nothing
    else --we can't find halt
      Just $ HaltUnreachable phase
    where
  --starts at a phase, maintains a list to explore, and a set of visited phases,
  --returns true if Halt is reachable ie if there is no proof
  --    current             to explore next, seen
  dfsToHalt :: Phase -> State ([Phase], Set Phase) Bool
  dfsToHalt current = do
    b1 <- try current False
    b2 <- try current True
    if b1 || b2 then pure True else do
      _2 . contains current .= True
      use _1 >>= \case
        --we won't find halt because there is no more to explore
        [] -> pure False
        (newPhase : newExploreList) -> do
          _1 .= newExploreList
          dfsToHalt newPhase
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


  phaseToTrans :: Phase -> Set Trans
  phaseToTrans phase = fromList $ fromMaybe Empty $ sequenceA
    [transitions ^. at (phase, False), transitions ^. at (phase, True)]

--
--the number of steps a machine has taken
type Steps = Int
type SimState = (Phase, Steps, Tape)
dispSimState :: SimState -> String
dispSimState (phase, steps, tape) = "after " <> show steps <> " steps, state: " <> show phase <> " tape: " <> dispTape tape

eqStates :: SimState -> SimState -> Bool
eqStates (p, _, t) (p', _, t') = (p == p') && (t == t')
--Unknown means we don't know how to make progress
--from the current state, because it isn't in the transition map
--Stop means the machine halted with the given tape
--Continue means the machine hasn't halted and the current state is given
--ContinueForever means the machine has been proven to run forever
data SimResult = Unknown Edge | Stop Steps Tape
  | Continue SimState | ContinueForever HaltProof deriving (Eq, Ord, Show)

initState :: SimState
initState = (Phase 0, 0, Tape [] False [])

simStep :: Turing -> SimState -> SimResult
simStep (Turing _ trans ) (i, steps, (Tape ls bit rs))
  = case trans ^. at (i, bit) of
    Nothing -> Unknown (i, bit)
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      Stop (steps + 1) $ tapeLeft $ Tape ls True rs
    Just (Step j newBit L) ->
      Continue $ (j, steps + 1, tapeLeft $ Tape ls newBit rs)
    Just (Step j newBit R) ->
      Continue $ (j, steps + 1, tapeRight $ Tape ls newBit rs)


--
--simulates a machine for the given number of steps, where the state is the number
--of steps taken so far
simulate :: Int -> SimState -> Turing -> State Steps SimResult
simulate ( (\i -> i <= 0) -> True) state _ = pure $ Continue state
simulate steps state t = do
  modify (+1)
  case simStep t state of
    result@(Unknown _) -> pure result
    result@(Stop _ _) -> pure result
    (Continue newState) -> simulate (steps - 1) newState t


--simulates a machine for the given number of steps, working to prove it runs forever

simulateHalt :: Int -> Turing -> State Steps SimResult
simulateHalt steps t = case simStep t initState of --start off Bigstate at initState
  result@(Unknown _) -> pure result
  result@(Stop _ _) -> pure result
  (Continue bigState1) -> do
    modify (+1)
    --step bigState again
    case simStep t bigState1 of --step bigState again
      result@(Unknown _) -> pure result
      result@(Stop _ _) -> pure result
      (Continue bigState2) -> case testHalt bigState2 t of
        Just haltProof -> pure $ ContinueForever haltProof
        --step littleState once
        Nothing -> case simStep t initState of --start off littleState at initState
          (Continue littleState1)
            -> simulateHaltHelper (steps - 1) (littleState1, bigState2) t
          _ -> error "small state didn't continue, but we already checked it does"
  where
  --first element of tuple is smallStep, second is bigStep, advancing at twice the rate
  --if smallStep ever == bigstep, then we have found a cycle
  simulateHaltHelper :: Int -> (SimState, SimState) -> Turing -> State Steps SimResult
  simulateHaltHelper ( (\i -> i <= 0) -> True) (_, state) _ = pure $ Continue state
  simulateHaltHelper _ (uncurry eqStates -> True) _ = do
    stepsTaken <- get
    pure $ ContinueForever $ Cycle (stepsTaken `div` 2) stepsTaken
  simulateHaltHelper steps (littleState, bigState) t = do
    --trace ("little then big\n" <> show littleState <> "\n" <> show bigState <> "\n") $
    modify (+1)
    --step bigState once
    case simStep t bigState of
      result@(Unknown _) -> pure result
      result@(Stop _ _) -> pure result
      (Continue bigState1) -> do
        modify (+1)
        --step bigState again
        case simStep t bigState1 of
          result@(Unknown _) -> pure result
          result@(Stop _ _) -> pure result
          (Continue bigState2) -> case testHalt bigState2 t of
            Just haltProof -> pure $ ContinueForever haltProof
            --step littleState once
            Nothing -> case simStep t littleState of
              (Continue littleState1)
                -> simulateHaltHelper (steps - 1) (littleState1, bigState2) t
              _ -> error "small state didn't continue, but we already checked it does"

dispResult :: SimResult -> String
dispResult (Unknown edge) = "Simulating got stuck on " <> show edge
dispResult (Stop steps tape) = "Simulating finished after " <> show steps <> " steps, with the tape: " <> dispTape tape
dispResult (Continue state) = "Simulating didn't finish, we reached state: " <> dispSimState state
dispResult (ContinueForever proof) = "we proved the machine will go forever via: " <> show proof

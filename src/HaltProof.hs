module HaltProof where
import Relude
import Control.Lens

import Beaver

--the type of proofs that a TM will not halt
-- - HaltUnreachable means the Halt state is never transitioned to from the current state
--   and any states it transitions to
-- - Cycle means that the state reached after a number of steps and a greater number
--   of steps is identical
-- - OffToInfinitySimple means that after the given number of steps, the machine will
--   continue off in the given direction infintitely, never changing states
data HaltProof
  = HaltUnreachable Phase
  | Cycle Steps Steps
  | OffToInfinitySimple Steps Dir
  deriving (Eq, Ord, Show)


testHalt :: SimState -> Turing -> Maybe HaltProof
testHalt state@(phase, _, tape) t@(Turing stateCount transitions)
  =
    infiniteLeft state t
  <|> infiniteRight state t
  <|>
  evalState (dfsToHalt phase phase) (Empty, Empty)
  where
  --starts at a phase, maintains a list to explore, and a set of visited phases,
  --returns a proof of Halt's unreachability, if available
  -- Note that "first" is the very starting phase, used for the proof only
  --          first      current      to explore next, seen
  dfsToHalt :: Phase -> Phase -> State ([Phase], Set Phase) (Maybe HaltProof)
  dfsToHalt first current = do
    b1 <- try current False
    b2 <- try current True
    if b1 || b2
      then pure Nothing --they found halt, so we have no proof
      else do
        _2 . contains current .= True
        use _1 >>= \case
          --we won't find halt because there is no more to explore
          [] -> pure $ Just $ HaltUnreachable first
          (newPhase : newExploreList) -> do
            _1 .= newExploreList
            dfsToHalt first newPhase
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
  infiniteLeft :: SimState -> Turing -> Maybe HaltProof
  --suppse we are all the way at the left side of the tape, looking at a False
  infiniteLeft (phase, steps, Tape [] False rs) (Turing{transitions = trans}) =
  --and when we transition from this phase and a false, we step left, and stay in the
  --same phase (doesn't matter what we write)
      case trans ^. at (phase,False) of
        --then this pattern repeats forever and we never halt
        --TODO :: this phase name overwrites the previous phase
        Just (Step (((==) phase) -> True) _ L) -> Just $ OffToInfinitySimple steps L
        --else give up
        _ -> Nothing
  infiniteLeft _ _ = Nothing
  --this is analagous to the other case, but mirrored
  -- TODO :: refactor this to not duplicate so much code
  infiniteRight :: SimState -> Turing -> Maybe HaltProof
  infiniteRight (phase, steps, Tape ls False []) (Turing{transitions = trans}) =
    case trans ^. at (phase, False) of
      Just (Step (((==) phase) -> True) _ R) -> Just $ OffToInfinitySimple steps R
      _ -> Nothing
  infiniteRight _ _ = Nothing
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

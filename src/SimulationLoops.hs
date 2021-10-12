module SimulationLoops where 

import Relude 
import Control.Lens
import Data.List (maximumBy, foldl1)
import Prettyprinter

import Turing
import ExpTape
import Count
import HaltProof
import Results
import Glue
import SimulateSkip 
import Induction
import Skip
import Util 


type SimOneAction = Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState

data MultiResult a = UnknownEdge Edge 
                 | Result (SimResult (ExpTape Bit InfCount)) 
                 | NewState a
                    deriving (Eq, Ord, Show, Functor) 
type SimMultiAction = Turing -> SimState -> MultiResult SimState 

instance Applicative MultiResult where 
  pure = return 
  x1 <*> x2 = x1 >>= flip fmap x2

instance Monad MultiResult where 
  return = NewState 
  (>>=) :: MultiResult a -> (a -> MultiResult b) -> MultiResult b 
  k >>= f = case k of 
    NewState a -> f a 
    UnknownEdge e -> UnknownEdge e 
    Result r -> Result r 

simulateOneMachineOuterLoop :: NonEmpty SimOneAction -> Turing -> SimResult (ExpTape Bit InfCount)
simulateOneMachineOuterLoop updateFuncs startMachine = case updatesList of
  Right _ -> error "oh no"
  Left res -> res
  where
  bigUpdateFunc :: SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
  bigUpdateFunc = foldl1 (>=>) ((&) startMachine <$> updateFuncs)
  iterateM :: (Monad m) => (a -> m a) -> a -> m [a]
  iterateM k init = do
    res <- k init
    (:) res <$> iterateM k res
  updatesList :: Either (SimResult (ExpTape Bit InfCount)) [SimState]
  updatesList = iterateM bigUpdateFunc $ initSkipState startMachine

simulateManyMachinesOuterLoop :: NonEmpty SimMultiAction -> Turing -> [SimResult (ExpTape Bit InfCount)]
simulateManyMachinesOuterLoop updateFuncs startMachine = loop (startMachine, startState) [] [] where 
  startState :: SimState 
  startState = initSkipState startMachine 
  bigUpdateFunc :: Turing -> SimState -> MultiResult SimState 
  bigUpdateFunc machine = foldl1 (>=>) ((&) machine <$> updateFuncs)
  loop :: (Turing, SimState) -> [(Turing, SimState)]
    -> [SimResult (ExpTape Bit InfCount)] -> [SimResult (ExpTape Bit InfCount)]
  loop cur@(curMachine, curState) todo !prevRes = case uncurry bigUpdateFunc cur of 
    NewState newState -> loop (curMachine, newState) todo prevRes 
    Result result -> recurse todo (result : prevRes) 
    UnknownEdge e -> recurse ((makeNewState e curState <$> branchOnEdge e curMachine) <> todo) prevRes
  makeNewState :: Edge -> SimState -> Turing -> (Turing, SimState) 
  makeNewState edge state machine = (machine, state & s_book %~ updateBook edge machine)
  recurse :: [(Turing, SimState)] -> [SimResult (ExpTape Bit InfCount)] -> [SimResult (ExpTape Bit InfCount)]
  recurse [] results = results 
  recurse (next : todos) results = loop next todos results 

liftOneToMulti :: SimOneAction -> SimMultiAction 
liftOneToMulti action machine state = case action machine state of 
  Left res -> Result res 
  Right newState -> NewState newState 
  
liftModifyState :: (SimState -> SimState) -> (Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState)
liftModifyState f _t = Right . f 

liftModifyStateMulti :: (SimState -> SimState) -> SimMultiAction 
liftModifyStateMulti = liftOneToMulti . liftModifyState 

runAtCount :: Int -> SimOneAction -> SimOneAction 
runAtCount n act m state = if state ^. s_counter == n then act m state else pure state 

addSkipToStateOrInf :: Skip Bit -> SkipOrigin Bit -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState 
addSkipToStateOrInf skip origin state = if skipGoesForever skip && skipAppliedInHist skip (state ^. s_history)
  then Left (ContinueForever (SkippedToInfinity (state ^. s_steps) skip))
  else Right $ state & s_book %~ addSkipToBook skip origin 

--this is pretty copied from "simulateOneMachine"
simulateStepTotalLoop :: Int -> Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
simulateStepTotalLoop limit machine (SimState ph tape book steps trace hist histSet counter) = if steps > limit
  then Left $ Continue steps ph tape
  else case skipStep machine book ph tape of
  Unknown e -> error $ "edge undefined" <> show e
  MachineStuck -> error "machinestuck "
  Stopped c newTape _skipUsed -> Left $ Halted (steps + infCountToInt c) newTape
  Stepped c newPh newTape skipUsed -> case c of
    Infinity -> Left $ ContinueForever (SkippedToInfinity steps skipUsed)
    c -> Right $ SimState newPh newTape book (steps + infCountToInt c) (skipUsed : trace) hist histSet $ counter + 1

gluePreviousTwoSkips :: SimState -> SimState
gluePreviousTwoSkips state = state & s_book .~ newBook where
  book = state ^. s_book
  newBook = case state ^. s_trace of
    [] -> book
    [_] -> book
    skip : prevSkip : _rest -> case glueSkips prevSkip skip of
      Left err -> error $ "used two skips in a row but couldn't glue:\n"
        <> "reason: " <> err <> "\n" <> show (pretty prevSkip)
        <> "\nsecond skip\n" <> show (pretty skip)
      Right gluedSkip -> addSkipToBook gluedSkip (Glued prevSkip skip) book

recordHist :: SimState -> SimState
recordHist state = state & s_history %~ (histEnt :) where
  histEnt = (state ^. s_phase, state ^. s_tape)

checkSeenBefore :: SimOneAction 
checkSeenBefore _machine state = case state ^. s_history_set . at histEnt of
  Just prevStepCount -> Left $ ContinueForever $ Cycle prevStepCount curStepCount 
  Nothing -> Right $ state & s_history_set . at histEnt ?~ curStepCount
  where 
  histEnt = (state ^. s_phase, state ^. s_tape)
  curStepCount = state ^. s_steps

--applies the skip to everything in the list, checks if any of them have just 
skipAppliedInHist :: Skip Bit -> [(Phase, ExpTape Bit InfCount)] -> Bool 
skipAppliedInHist skip hist = any (has _Just) $ applySkip skip <$> hist 

attemptInductionGuess :: Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
attemptInductionGuess machine state = case guessInductionHypothesis hist of 
  Nothing -> Right state 
  --try to prove the skip by induction 
  Just skip -> trace ("guessed a skip:\n" <> show (pretty skip)) $ 
    case proveInductively 20 machine (state ^. s_book) skip (BoundVar 0) of 
      Left fail -> trace (toString fail) $ Right state 
      Right skipOrigin -> addSkipToStateOrInf skip skipOrigin state 
        -- if skipGoesForever skip && skipAppliedInHist skip hist 
        -- then Left (ContinueForever (SkippedToInfinity (state ^. s_steps) skip))
        -- else Right $ state & s_book %~ addSkipToBook skip skipOrigin 
  where 
    hist = reverse (state ^. s_history)

attemptEndOfTapeGlueProof :: SimOneAction 
attemptEndOfTapeGlueProof _machine state = rightAddedState where
  hist = state ^. s_history 
    --we're going to need to look at the history, find all the places the machine was at a specific 
  --end of the tape, then attempt to glue between those 

  makeSkipFromTimes :: [Bool] -> Either Text (Skip Bit, SkipOrigin Bit)
  makeSkipFromTimes times = do 
    (last, sndLast) <- case reverse $ filter snd $ zip [0, 1 .. ] times of
      [] -> Left "never at left side"
      [_] -> Left "at left side only once"
      (last, _) : (sndLast, _) : _rest -> pure (last, sndLast) 

    let skipRange = case nonEmpty $ slice sndLast last $ state ^. s_trace of
          Nothing -> error $ "first slice equalled last? wacked:" <> show last 
          Just ne -> ne 
    (,GlueStepRange sndLast last) <$> glueMany skipRange 

  maybeLeftSkip :: Either Text (Skip Bit, SkipOrigin Bit) 
  maybeLeftSkip = makeSkipFromTimes $ wasAtLeft . snd <$> hist
  maybeRightSkip = makeSkipFromTimes $ wasAtRight . snd <$> hist
  wasAtLeft (ExpTape ls _p _rs) = ls == [(False, Infinity)]
  wasAtRight (ExpTape _ls _p rs) = rs == [(False, Infinity)]
  addFailSkipToState skip state = either (const $ Right state) (flip (uncurry addSkipToStateOrInf) state) skip
  leftAddedState :: Either (SimResult (ExpTape Bit InfCount)) SimState
  leftAddedState = addFailSkipToState maybeLeftSkip state 
  rightAddedState = addFailSkipToState maybeRightSkip =<< leftAddedState 
  
loopSimulateSkip :: Int -> Turing -> SimResult (ExpTape Bit InfCount)
loopSimulateSkip limit = simulateOneMachineOuterLoop $ pure $ simulateStepTotalLoop limit

indGuessLoop ::  Int -> Turing -> SimResult (ExpTape Bit InfCount)
indGuessLoop limit = simulateOneMachineOuterLoop $ 
  simulateStepTotalLoop limit :| [liftModifyState recordHist, runAtCount 100 attemptInductionGuess]


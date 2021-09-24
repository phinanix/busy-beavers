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

type SimAction = Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState

simulateOneMachineOuterLoop :: NonEmpty (Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState) -> Turing -> SimResult (ExpTape Bit InfCount)
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

liftModifyState :: (SimState -> SimState) -> (Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState)
liftModifyState f _t = Right . f 

runAtCount :: Int -> SimAction -> SimAction 
runAtCount n act m state = if state ^. s_counter == n then act m state else pure state 

--this is pretty copied from "simulateOneMachine"
simulateStepTotalLoop :: Int -> Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
simulateStepTotalLoop limit machine (SimState ph tape book steps trace hist counter) = if steps > limit
  then Left $ Continue steps ph tape
  else case skipStep machine book ph tape of
  Unknown e -> error $ "edge undefined" <> show e
  MachineStuck -> error "machinestuck "
  Stopped c newTape _skipUsed -> Left $ Halted (steps + infCountToInt c) newTape
  Stepped c newPh newTape skipUsed -> case c of
    Infinity -> Left $ ContinueForever (SkippedToInfinity steps skipUsed)
    c -> Right $ SimState newPh newTape book (steps + infCountToInt c) (skipUsed : trace) hist $ counter + 1

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
recordHist state = state & s_history %~ (:) curTape where
  curTape = state ^. s_tape

attemptInductionGuess :: Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
attemptInductionGuess _machine state = case guessInductionHypothesis hist of 
  Just skip -> Left $ InductionGuess skip 
  Nothing -> Right state 
  where 
    hist = reverse (state ^. s_history)

loopSimulateSkip :: Int -> Turing -> SimResult (ExpTape Bit InfCount)
loopSimulateSkip limit = simulateOneMachineOuterLoop $ pure $ simulateStepTotalLoop limit

indGuessLoop ::  Int -> Turing -> SimResult (ExpTape Bit InfCount)
indGuessLoop limit = simulateOneMachineOuterLoop $ 
  simulateStepTotalLoop limit :| [liftModifyState recordHist, runAtCount 100 attemptInductionGuess]


module MoreSimulationLoops where

import Relude
import qualified Relude.Unsafe as Unsafe
import Control.Lens
import Prettyprinter
import qualified Data.Map as M

import Turing
import ExpTape
import Count
import Results
import SimulateSkip
import Skip
import Control.Exception (assert)
import Induction
import SimulationLoops
import Util
import HaltProof
import LinRecurrence

attemptInductionGuess :: Turing -> SimState
  -> Either (SimResult (ExpTape Bit InfCount)) SimState
attemptInductionGuess machine state = trace "attempted" $
  case guessInductionHypothesis hist dispHist of
    Left msg -> traceShow msg $ Right state
    --try to prove the skip by induction 
    Right skip -> trace ("guessed a skip:\n" <> show (pretty skip)) $
      case proveInductively 20 machine (state ^. s_book) skip (BoundVar 0) of
        Left (fail, _config) -> trace (toString fail) $ Right state
        Right skipOrigin -> trace ("succeeded") $
          addSkipToStateOrInf skip skipOrigin state
  where
    hist =  state ^. s_history
    dispHist = state ^. s_disp_history

--Note! this function is outdated
indGuessLoop ::  Int -> Turing -> OneLoopRes
indGuessLoop limit = simOneFromStartLoop $
  simulateStepTotalLoop limit :| [liftModifyState recordHist,
   liftModifyState recordDispHist,
   runAtCount 100 attemptInductionGuess]

makeIndGuess :: Int -> Turing -> Either Text (Skip Count Bit)
makeIndGuess = uncurry guessInductionHypothesis .: getTwoHistAfterTime

getRecurRes :: Int -> Turing -> Maybe HaltProof
getRecurRes stepCount turing = detectLinRecurrence tapeHist rsHist where
  tapeHist = guessingState ^. s_history
  rsHist = guessingState ^. s_readshift_history
  guessingState = getStateAfterTime stepCount turing

{-
plan for integrating proveInductivelyIMeanIT into the main loop:
we need to write a function which checks whether a skip goes forever in already known history
then we change the return type of proveInd to return the new skip if possible
then we write a function which runs proveInd, if it succeeds uses chainArbitrary, 
and then checks whether the skip runs forever
-}
proveByInd :: SimOneAction
proveByInd machine state = --force $ --trace ("proveByInd on:\n" <> showP machine) $ 
 case eTProof of
  Left _msg -> Right newState
  Right hp -> Left $ ContinueForever hp
  where
  hist = state ^. s_history
  dispHist =  state ^. s_disp_history
  (newbook, eTSkip) = let ans = proveInductivelyIMeanIT machine (state ^. s_book) (state ^. s_steps) hist dispHist
    in
      --trace ("etskip:\n" <> showP (ans ^. _2)) 
      ans
  newState = state & s_book .~ newbook
  eTArbSkip = let ans = chainArbitrary =<< eTSkip in
    --trace ("etarbskip:\n" <> showP ans) 
    ans
  eTProof = let ans = flip skipAppliesForeverInHist hist =<< eTArbSkip in
    --trace ("etproof:\n" <> show ans) 
    ans

proveSimply :: SimOneAction
proveSimply machine state = case mbProof of
  Left _txt -> Right state
  Right hp -> Left $ ContinueForever hp
  where
  mbProof = do
    indHyp <- guessInductionHypothesis (state ^. s_history) (state ^. s_disp_history)
    first fst $ proveBySimulating 100 machine (state ^. s_book) indHyp
    arbSkip <- chainArbitrary indHyp
    skipAppliesForeverInHist arbSkip (state ^. s_history)

{-
goal: write a function which runs 1) LR 2) cycle finding 3) end-of-tape
and checks that 1 iff (2 or 3)
it returns the LR proof if there is one, and it raises if the assert fails
-}

proveByLR :: SimOneAction
proveByLR _machine state = case maybeProof of
    Nothing -> Right state
    Just hp -> Left $ ContinueForever hp
  where
  maybeProof = detectLinRecurrence (state ^. s_history) (state ^. s_readshift_history)

proveLRLoop :: Int -> Turing -> OneLoopRes
proveLRLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [liftModifyState recordHist, liftModifyState recordDispHist, 
    runAtCount (limit-2) proveByLR]

canProveLR :: Int -> Turing -> Bool 
canProveLR limit m = case proveLRLoop limit m of 
  (ContinueForever (LinRecur _ _), _ne) -> True 
  (ContinueForever (SkippedToInfinity _ _), _ne) -> True 
  _ -> False 

proveCycleLoop :: Int -> Turing -> OneLoopRes 
proveCycleLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [checkSeenBefore] 

canProveCycle :: Int -> Turing -> Bool 
canProveCycle limit m = case proveCycleLoop limit m of 
  (ContinueForever (Cycle _ _), _ne) -> True 
  (ContinueForever (SkippedToInfinity _ _), _ne) -> True 
  _ -> False 

proveEOTLoop :: Int -> Turing -> OneLoopRes 
proveEOTLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [liftModifyState recordHist, liftModifyState recordDispHist, 
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof]

canProveEOT :: Int -> Turing -> Bool 
canProveEOT limit m = case proveEOTLoop limit m of 
  (ContinueForever (OffToInfinityN _ _), _) -> True 
  (ContinueForever (SkippedToInfinity _ _), _ne) -> True 
  _ -> False 

proveOEOTLoop :: Int -> Turing -> OneLoopRes 
proveOEOTLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [liftModifyState recordHist, liftModifyState recordDispHist, 
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof]

canProveOEOT :: Int -> Turing -> Bool 
canProveOEOT limit m = case proveOEOTLoop limit m of 
  (ContinueForever (OffToInfinityN _ _), _) -> True 
  _ -> False 

checkLRAssertOneMachine :: Int -> Turing -> Maybe Text
checkLRAssertOneMachine limit unfinishedM = if toAssert then Nothing else Just msg where 
  m = fillInMachine unfinishedM
  lrWorked = canProveLR limit m 
  cycleWorked = canProveCycle limit m 
  eotWorked = canProveEOT limit m 
  otherEotWorked = canProveOEOT limit m
  notBothEot = not (eotWorked && otherEotWorked && not cycleWorked)
  lrComplementsWorked = cycleWorked || eotWorked || otherEotWorked
  lrIffComplements = lrWorked == lrComplementsWorked

  toAssert = lrIffComplements && notBothEot
  msg = "assert failed on:\n" <> showP m 
    <> " " <> showP [lrWorked, cycleWorked, eotWorked, otherEotWorked]

--todo run at count being measured in big steps while limit is measured in small steps is bad
indProveLoop :: Int -> Turing -> OneLoopRes
indProveLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof,
  runAtCount 50 proveByInd
  ]

enumerateMachinesLoop :: Int -> Turing -> [(Turing, SimResult (ExpTape Bit InfCount))]
enumerateMachinesLoop limit = simulateManyMachinesOuterLoop (const Nothing) $
  simulateStepPartial limit :| []

checkLRAssertManyMachines :: Int -> Turing -> [Text]
checkLRAssertManyMachines limit startMachine = catMaybes texts where 
  machines = fst <$> enumerateMachinesLoop limit startMachine
  texts = checkLRAssertOneMachine limit <$> machines 

indProveLoopMany :: Int -> Turing -> [(Turing, SimResult (ExpTape Bit InfCount))]
indProveLoopMany limit = simulateManyMachinesOuterLoop backwardSearch $ simulateStepPartial limit
  :| (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof,
  runAtCount 190 proveByInd
  ])

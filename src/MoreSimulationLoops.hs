module MoreSimulationLoops where

import Relude
import qualified Relude.Unsafe as Unsafe
import Control.Lens
import Prettyprinter

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

attemptInductionGuess :: Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
attemptInductionGuess machine state = trace "attempted" $ case guessInductionHypothesis hist dispHist of
  Left msg -> traceShow msg $ Right state
  --try to prove the skip by induction 
  Right skip -> trace ("guessed a skip:\n" <> show (pretty skip)) $
    case proveInductively 20 machine (state ^. s_book) skip (BoundVar 0) of
      Left (fail, _config) -> trace (toString fail) $ Right state
      Right skipOrigin -> trace ("succeeded") $ addSkipToStateOrInf skip skipOrigin state
  where
    hist =  state ^. s_history
    dispHist = state ^. s_disp_history

--Note! this function is outdated
indGuessLoop ::  Int -> Turing -> OneLoopRes
indGuessLoop limit = simOneFromStartLoop $
  simulateStepTotalLoop limit :| [liftModifyState recordHist, liftModifyState recordDispHist, runAtCount 100 attemptInductionGuess]

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

--todo run at count being measured in big steps while limit is measured in small steps is bad
indProveLoop :: Int -> Turing -> OneLoopRes
indProveLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof,
  runAtCount 200 proveByInd
  ]

indProveLoopMany :: Int -> Turing -> [_]
indProveLoopMany limit = simulateManyMachinesOuterLoop backwardSearch $ simulateStepPartial limit
  :| (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof,
  runAtCount 50 proveByInd
  ])

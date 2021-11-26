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
import Induction ( proveInductively, guessInductionHypothesis )
import SimulationLoops

attemptInductionGuess :: Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
attemptInductionGuess machine state = case guessInductionHypothesis hist dispHist of
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
    dispHist = reverse (state ^. s_disp_history)

indGuessLoop ::  Int -> Turing -> OneLoopRes
indGuessLoop limit = simOneFromStartLoop $
  simulateStepTotalLoop limit :| [liftModifyState recordHist, runAtCount 100 attemptInductionGuess]

makeIndGuess :: Int -> Turing -> Maybe (Skip Count Bit)
makeIndGuess stepCount turing = guessInductionHypothesis histToUse dispHist where
  guessingState = getStateAfterTime stepCount turing
  histToUse = reverse $ guessingState ^. s_history 
  dispHist = reverse $ guessingState ^. s_disp_history
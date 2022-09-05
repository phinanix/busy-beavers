module MoreSimulationLoopsSpec where

import Relude
import Control.Lens
import Prettyprinter

import Test.Hspec
import Test.QuickCheck

import Turing
import Count
import TuringExamples
import SimulateSkip
import Induction
import ExpTape
import Skip
import SimulationLoops
import Results
import HaltProof
import MoreSimulationLoops
import Util

spec :: Spec
spec = do
  describe "indProveLoop" $ do
    --TODO we should be able to prove this machine runs forever
    it "works on a machine which tripped it up" $
      fst (indProveLoop 200 machineBreaksIndGuess) `shouldSatisfy` has _Continue
    --TODO we should be able to prove this machine runs forever
    it "does not produce machinestuck" $ do
      fst (indProveLoop 200 machineStuckMachine) `shouldSatisfy` const True
    -- it "doesn't crash on a machine which made it crash" $ do
    --   fst (indProveLoop 200 some_kind_of_bincounter) `shouldSatisfy` has _Continue
    it "satisifes the LR assert" $ do
      property (\(t :: Turing) -> checkLRAssertOneMachine 120 t `shouldBe` Nothing)
  -- describe "indProveLoopMany" $ do 
  --  it "works on machines of size 3" $ 
  --     -- this appears to be an infinite loop !? :c
  --     length (indProveLoopMany 200 (startMachine1 3)) `shouldBe` 4052
  describe "makeAdditiveSkip" $ do 
    it "works on a particular case" $ do
      {- 
      (F, 1) (T, 42) F (F, 47)
             (T, 90) F
      -}
      let startTape = ExpTape [(Bit True, FinCount 42), (Bit False, FinCount 1)] (Bit False)
                              [(Bit False, FinCount 47)]
          endTape = ExpTape [(Bit True, FinCount 90)] (Bit False) []
      makeAdditiveSkip (Phase 0) startTape endTape `shouldBe` Just (Skip 
          (Config (Phase 0) [(Bit True, boundVarCount (BoundVar 0) 1), (Bit False, FinCount 1)]
            (Bit False) [(Bit False, FinCount 47)])
          (SkipStepped (Phase 0) (Middle (ExpTape [(Bit True, FinCount 48 <> boundVarCount (BoundVar 0) 1)]
                (Bit False) [])))
          Empty 
        )
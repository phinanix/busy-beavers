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
      fst (indProveLoop 200 machineStuckMachine) `shouldSatisfy` (not . has _MachineStuckRes)
    it "doesn't crash on a machine which made it crash" $ do
      fst (indProveLoop 200 some_kind_of_bincounter) `shouldSatisfy` has _Continue
    it "satisifes the LR assert" $ do
      property (\(t :: Turing) -> checkLRAssertOneMachine 120 t `shouldBe` Nothing)
--  describe "indProveLoopMany" $ do 
--    it "works on machines of size 3" $ 

      --this appears to be an infinite loop !? :c
      --length (indProveLoopMany 200 (startMachine1 3)) `shouldBe` 4052

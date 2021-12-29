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
    it "works on a machine which tripped it up" $
      fst (indProveLoop 200 machineBreaksIndGuess) `shouldSatisfy` has _ContinueForever
    it "does not produce machinestuck" $ do
      fst (indProveLoop 200 machineStuckMachine) `shouldSatisfy` has _ContinueForever 
--  describe "indProveLoopMany" $ do 
--    it "works on machines of size 3" $ 

      --this appears to be an infinite loop !? :c
      --length (indProveLoopMany 200 (startMachine1 3)) `shouldBe` 4052

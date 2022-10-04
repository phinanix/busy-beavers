module LinRecurrenceSpec where 


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
import LinRecurrence 


spec :: Spec
spec = do
  describe "hasPair" $ do
    it "finds a pair" $
      hasPair "0123456289" `shouldBe` Just (2, 7)
    it "doesn't find a pair" $
      hasPair "abcdefghijklmnopqrstuvwxyz" `shouldBe` Nothing
  describe "liveTapeRegion" $ do 
    it "finds an example" $ 
      liveRegion [(Bit False, NotInfinity One), (Bit True, NotInfinity $ FinCount 3), (Bit False, Infinity)]
      `shouldBe` 4
  describe "detectLinRecurrence" $ do 
    it "finds a recurrence" $ 
      getRecurRes 200 machineStuckMachine `shouldBe` Just (LinRecur 0 116)
    it "doesn't find a recurrence for a halting machine" $ 
      getRecurRes 12 bb3 `shouldBe` Nothing
    it "doesn't find a recurrence for a counting machine" $
      getRecurRes 250 binaryCounterTFTT `shouldBe` Nothing 
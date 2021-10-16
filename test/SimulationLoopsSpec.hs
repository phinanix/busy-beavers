module SimulationLoopsSpec where

import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck

import Turing
import Count
import ExpTape 
import Results 
import SimulationLoops 

import HaltProof
import TuringExamples

loopForEndOfTapeGlue :: Int -> Turing -> SimResult (ExpTape Bit InfCount)
loopForEndOfTapeGlue limit = simulateOneMachineOuterLoop $ 
    simulateStepTotalLoop limit :| [attemptEndOfTapeGlueProof]

c = finiteCount 

test :: InfCount 
test = NotInfinity (c 2)

spec :: Spec 
spec = do 
  describe "attemptEndOfTapeGlueProof" $ do 
    xit "proves a simple goes forever machine" $ do 
      loopForEndOfTapeGlue 100 goesLeftForever `shouldBe` ContinueForever (OffToInfinityN 1 L)
    it "does not prove a machine that doesn't halt in this way" $ do 
      loopForEndOfTapeGlue 100 weird3 `shouldBe`  
        Continue 101 (Phase 2) (ExpTape [(False,NotInfinity (c 2)),(True,NotInfinity (c 1)),(False,Infinity)] False [(True,NotInfinity (c 2)),(False,Infinity)]) (-3)
module SimulationLoopsSpec where

import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck

import Turing
import Count
import ExpTape 
import Results 
import SimulateSkip
import SimulationLoops 

import HaltProof
import TuringExamples

c = finiteCount 

test :: InfCount 
test = NotInfinity (c 2)

spec :: Spec 
spec = do 
  describe "attemptEndOfTapeGlueProof" $ do 
    it "proves a simple goes forever machine" $ do 
      fst (loopForEndOfTapeGlue 100 goesLeftForever) `shouldBe` ContinueForever (OffToInfinityN 2 L)
    it "does not prove a machine that doesn't halt in this way" $ do 
      fst (loopForEndOfTapeGlue 100 weird3) `shouldBe`  
        Continue 101 (Phase 2) 
          (ExpTape [(Bit False,NotInfinity (c 2)),(Bit True,NotInfinity (c 1)),(Bit False,Infinity)] 
           (Bit False)
           [(Bit True,NotInfinity (c 2)),(Bit False,Infinity)])
           (-3)
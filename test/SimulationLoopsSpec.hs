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
        Continue 128 
          (Phase 2) 
          (ExpTape 
            [(Bit True,NotInfinity (Count 2 (fromList []) (fromList []))),(Bit False,NotInfinity (Count 1 (fromList []) (fromList []))),(Bit True,NotInfinity (Count 1 (fromList []) (fromList []))),(Bit False,Infinity)] 
            (Bit False)
            [(Bit True,NotInfinity (Count 1 (fromList []) (fromList []))),(Bit False,Infinity)]) (-2)
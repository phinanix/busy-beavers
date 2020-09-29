module SkipSpec where

--
import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)

import Count hiding (num)
import Turing
import ExpTape
import Skip

num = finiteCount

spec :: Spec
spec = do
  describe "matchTapeHeads" $ do
    it "matches identical values" $ do
      runEquationState (matchTapeHeads (False, finiteCount 5) (False, finiteCount 5))
        `shouldBe` Just PerfectH
    --
    it "matches smaller against larger values" $ do
      runEquationState (matchTapeHeads (False, finiteCount 5) (False, finiteCount 8))
        `shouldBe` Just (TapeHLeft (False, finiteCount 3))
    --
    it "matches a var against a num " $ do
      runEquationState (matchTapeHeads (False, varCount 5) (False, finiteCount 5))
        `shouldBe` Just PerfectH
    --
    it "matches a var against several vars" $ do
      runEquationState (matchTapeHeads (False, varCount 5) (False, varCount 0 <> varCount 0 <> varCount 5))
        `shouldBe` Just PerfectH
  describe "matchTape" $ do
    it "matches a simple example" $ do
      runEquationState (matchBitTape [(False, num 3)] [(False, num 5), (True, num 1)])
        `shouldBe` Just (NewTape [(False, num 2), (True, num 1)])

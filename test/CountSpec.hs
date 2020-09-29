module CountSpec where

--
import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)

import Count

spec :: Spec
spec = do
  describe "matchCount" $ do
    it "matches equal numbers" $ do
      matchCount (finiteCount 5) (finiteCount 5) `shouldBe` Just Empty

    it "matches a bigger second number" $ do
      matchCount (finiteCount 5) (finiteCount 7) `shouldBe` Just (finiteCount 2)

    it "fails a bigger first number" $ do
      matchCount (finiteCount 7) (finiteCount 5) `shouldBe` Nothing

    it "matches a var against two vars" $ do
      matchCount (varCount 0) (varCount 1 <> varCount 2) `shouldBe` Just Empty

    it "matches a var against itself plus one" $ do
      matchCount (varCount 0) (finiteCount 1 <> varCount 0) `shouldBe` Just Empty

    it "fails a var plus five against a bare var" $ do
      matchCount (varCount 0 <> finiteCount 5) (varCount 10000) `shouldBe` Nothing

    it "matches a var against a finite count" $ do
      matchCount (varCount 1) (finiteCount 5) `shouldBe` Just Empty
  describe "equationStae" $ do
    it "getting a pure is Just" $ do
      property (\(c :: Char) -> runEquationState (pure c) `shouldBe` Just c)

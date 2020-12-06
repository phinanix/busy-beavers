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
inum = finiteInfCount

spec :: Spec
spec = do
  pure ()
--   describe "matchTapeHeads" $ do
--     it "matches identical values" $ do
--       getEquations (matchTapeHeads (NotVar False, num 5) (False, inum 5))
--         `shouldBe` Just PerfectH
--     --
--     it "matches smaller against larger values" $ do
--       getEquations (matchTapeHeads (NotVar False, num 5) (False, inum 8))
--         `shouldBe` Just (TapeHLeft (False, inum 3))
--     --
--     it "matches a var against a num " $ do
--       getEquations (matchTapeHeads (NotVar False, newBoundVar 5) (False, inum 5))
--         `shouldBe` Just PerfectH
--     --
--     it "matches a var against several vars" $ do
--       getEquations (matchTapeHeads (NotVar False, newBoundVar 5)
--         (False, newInfBoundVar 0 <> newInfBoundVar 0 <> newInfBoundVar 5))
--         `shouldBe` Just PerfectH
--   describe "matchTape" $ do
--     it "matches a simple example" $ do
--       getEquations (matchBitTape
--         [(NotVar False, num 3)] [(False, inum 5), (True, inum 1)])
--         `shouldBe` Just (NewTape [(False, inum 2), (True, inum 1)])

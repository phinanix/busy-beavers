module CountSpec where

--
import Relude
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)
import Test.QuickCheck.Instances

import Count

getBitES :: Equations s -> Maybe s
getBitES = getEquations

matchAndGet :: Count -> Count -> Maybe Count
matchAndGet a b = getBitES $ matchCount a b

instance Arbitrary SymbolVar where 
  arbitrary = SymbolVar <$> arbitrary 

instance Arbitrary BoundVar where 
  arbitrary = BoundVar <$> arbitrary

instance Arbitrary Count where 
  arbitrary = liftA3 Count arbitrary (MonoidalMap <$> arbitrary) (MonoidalMap <$> arbitrary)

spec :: Spec
spec = do
  describe "matchCount" $ do
    it "matches equal numbers" $ do
      matchAndGet (finiteCount 5) (finiteCount 5) `shouldBe` Just Empty

    it "matches a bigger second number" $ do
      matchAndGet (finiteCount 5) (finiteCount 7) `shouldBe` Just (finiteCount 2)

    it "fails a bigger first number" $ do
      matchAndGet (finiteCount 7) (finiteCount 5) `shouldBe` Nothing

    it "matches a var against two vars" $ do
      matchAndGet (newBoundVar 0) (newBoundVar 1 <> newBoundVar 2) `shouldBe` Just Empty

    it "matches a var against itself plus one" $ do
      matchAndGet (newBoundVar 0) (finiteCount 1 <> newBoundVar 0) `shouldBe` Just Empty

    it "fails a var plus five against a bare var" $ do
      matchAndGet (newBoundVar 0 <> finiteCount 5) (newBoundVar 10000) `shouldBe` Nothing

    it "matches a var against a finite count" $ do
      matchAndGet (newBoundVar 1) (finiteCount 5) `shouldBe` Just Empty
  describe "equationState" $ do
    it "getting a pure is Just" $ do
      property (\(c :: Char) -> getBitES (pure c) `shouldBe` Just c)
  describe "likeTerms" $ do
    it "gets simple like terms" $ do 
      likeTerms (finiteCount 5) (newBoundVar 1 <> finiteCount 2) `shouldBe` (finiteCount 2, finiteCount 3, newBoundVar 1)
    it "satisfies the additive property" $ do 
      property (\ c d -> case likeTerms c d of 
        (likes, c', d') -> (likes <> c', likes <> d') `shouldBe` (c, d))

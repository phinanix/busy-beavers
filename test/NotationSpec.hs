module NotationSpec where

--
import Relude
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))

import Data.Char 
import qualified Data.Text as T

import Control.Exception
import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)
import Test.QuickCheck.Instances

import Turing
import TuringExamples
import Util
import Count
import Skip
import Notation

spec :: Spec
spec = do
  describe "notation parser" $ do
    it "should roundtrip" $ do
      property (\(t :: Turing) -> notationToMachine (machineToNotation t) `shouldBe` Right t)
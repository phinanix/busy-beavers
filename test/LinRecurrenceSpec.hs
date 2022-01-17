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

spec :: Spec
spec = do
  describe "recurr" $ do
    it "works on a simple case" $
      3 `shouldBe` 3
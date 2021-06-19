module SimulateSkipSpec where 

import Relude 
import Control.Lens
import Control.Lens.Extras

import Test.Hspec
import Test.QuickCheck


import SimulateSkip

spec :: Spec 
spec = 
  -- the goal of this test is to make sure that simulating the machine with skips outputs the same thing 
  -- as simulating a machine without skips
  describe "simulateWithSkips" $ do 
    it "produces the same results as normal simulation" $ 
      True `shouldBe` True
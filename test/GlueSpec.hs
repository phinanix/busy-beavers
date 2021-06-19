module GlueSpec where 

import Relude 
import Control.Lens
import Test.Hspec
import Test.QuickCheck

import Turing
import Count 
import ExpTape
import Skip 
import Glue

skipA :: Skip Bit 
skipA = Skip 
    (Config (Phase 0) [] False [])
    (EndSide (Phase 1) L [(False, One)])
    One
    False 

skipB :: Skip Bit 
skipB = Skip 
    (Config (Phase 1) [] False [])
    (EndSide (Phase 2) L [(True, One)]) 
    One
    False 

skipAB :: Skip Bit 
skipAB = Skip 
    -- (Config (Phase 0) [] (False, Side (finiteCount 2) R) [])
    (Config (Phase 0) [(False, One)] False [])
    (EndSide (Phase 2) L [(True, One), (False, One)])
    (finiteCount 2) 
    False
    
selfGlueSkip :: Skip Bit 
selfGlueSkip = Skip 
  (Config (Phase 1) [(True, One), (False, One)] False [])
  (EndMiddle $ Config (Phase 1) [(True, One)] False [(False, One)])
  (finiteCount 3) 
  False

twoSelfGlueSkip :: Skip Bit 
twoSelfGlueSkip = Skip 
  (Config (Phase 1) [(True, One), (False, finiteCount 2)] False [])
  (EndMiddle $ Config (Phase 1) [(True, One)] False [(False, finiteCount 2)]) 
  (finiteCount 6)
  False

-- the one which is wrong is the Right one
spec :: Spec 
spec = do 
  describe "glueSkips" $ do 
    it "glues two skips" $ do 
      glueSkips skipA skipB `shouldBe` Right skipAB  
    it "glues a skip to itself" $ do 
      glueSkips selfGlueSkip selfGlueSkip `shouldBe` Right twoSelfGlueSkip
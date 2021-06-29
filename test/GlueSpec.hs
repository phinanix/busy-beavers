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
import SimulateSkip

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

-- these two skips should glue, but based on my bb3 glueing runs same as vanilla test, 
-- the gluing algorithm nonsenically produces the skip 
-- input >F< F 
-- output <|(T, 1 + x)
-- which is not even legal in the first place (due to x being unbound in the input)
case2SkipA :: Skip Bit 
case2SkipA = oneStepSkip (Phase 1, False) (Phase 2) False R 

case2SkipB :: Skip Bit 
case2SkipB = infiniteSkip (Phase 2, False) True L 

-- calculated by hand, this is the "correct" output in this situation. there's actually a 
-- different correct output that preserves the x that I think might be better to output but 
-- I don't think the current algorithm can calculate. Of course, the first step is to output 
-- anything that is not wrong and then I can determine what makes sense as the best possible output
case2CorrectOutput :: Skip Bit 
case2CorrectOutput = Skip 
  (Config (Phase 1) [] False [(False, One)])
  (EndSide (Phase 2) L [(True, finiteCount 2)])
  (finiteCount 3) 
  False

-- the one which is wrong is the Right one
spec :: Spec 
spec = do 
  describe "glueSkips" $ do 
    it "glues two skips" $ do 
      glueSkips skipA skipB `shouldBe` Right skipAB  
    it "glues a skip to itself" $ do 
      glueSkips selfGlueSkip selfGlueSkip `shouldBe` Right twoSelfGlueSkip
    it "glues two skips case 2" $ do 
      glueSkips case2SkipA case2SkipB `shouldBe` Right case2CorrectOutput
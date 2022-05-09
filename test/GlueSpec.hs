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

skipA :: Skip Count Bit 
skipA = Skip 
    (Config (Phase 0) [] (Bit False) [])
    (EndSide (Phase 1) L [(Bit False, One)])
    One
    False 

skipB :: Skip Count Bit 
skipB = Skip 
    (Config (Phase 1) [] (Bit False) [])
    (EndSide (Phase 2) L [(Bit True, One)]) 
    One
    False 

skipAB :: Skip Count Bit 
skipAB = Skip 
    -- (Config (Phase 0) [] (False, Side (finiteCount 2) R) [])
    (Config (Phase 0) [(Bit False, One)] (Bit False) [])
    (EndSide (Phase 2) L [(Bit True, One), (Bit False, One)])
    (finiteCount 2) 
    False

selfGlueSkip :: Skip Count Bit 
selfGlueSkip = Skip 
  (Config (Phase 1) [(Bit True, One), (Bit False, One)] (Bit False) [])
  (EndMiddle $ Config (Phase 1) [(Bit True, One)] (Bit False) [(Bit False, One)])
  (finiteCount 3) 
  False

twoSelfGlueSkip :: Skip Count Bit 
twoSelfGlueSkip = Skip 
  (Config (Phase 1) [(Bit True, One), (Bit False, finiteCount 2)] (Bit False) [])
  (EndMiddle $ Config (Phase 1) [(Bit True, One)] (Bit False) [(Bit False, finiteCount 2)]) 
  (finiteCount 6)
  False

-- these two skips should glue, but based on my bb3 glueing runs same as vanilla test, 
-- the gluing algorithm nonsenically produces the skip 
-- input >F< F 
-- output <|(T, 1 + x)
-- which is not even legal in the first place (due to x being unbound in the input)
case2SkipA :: Skip Count Bit 
case2SkipA = oneStepSkip (Phase 1, Bit False) (Phase 2) (Bit False) R 

case2SkipB :: Skip Count Bit 
case2SkipB = infiniteSkip (Phase 2, Bit False) (Bit True) L 

-- calculated by hand, this is the "correct" output in this situation. there's actually a 
-- different correct output that preserves the x that I think might be better to output but 
-- I don't think the current algorithm can calculate. Of course, the first step is to output 
-- anything that is not wrong and then I can determine what makes sense as the best possible output
case2CorrectOutput :: Skip Count Bit 
case2CorrectOutput = Skip 
  (Config (Phase 1) [] (Bit False) [(Bit False, One)])
  (EndSide (Phase 2) L [(Bit True, finiteCount 2)])
  (finiteCount 3) 
  False

c = finiteCount 

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
  -- describe "glueDisplacements" $ do 
  --   it "glues things going the same way" $ do 
  --     glueDisplacements (OneDir L $ c 2) (OneDir L $ c 5) `shouldBe` (OneDir L $ c 7) 
  --   it "glues things going different ways" $ do 
  --     glueDisplacements (OneDir L $ c 1) (OneDir R $ c 8) `shouldBe` (OneDir R $ c 7)
  --   it "glues a thing adding to zero" $ do 
  --     glueDisplacements (OneDir L $ c 3) (OneDir R $ c 3) `shouldBe` (OneDir L $ c 0)
  --   it "glues a thing involving some variables" $ do 
  --     glueDisplacements (OneDir L $ Count 2 Empty (SingletonMap (BoundVar 0) (Sum 2))) 
  --       (OneDir L $ Count 5 (SingletonMap (SymbolVar 3) (Sum 1)) Empty) `shouldBe`
  --       (OneDir L $ Count 7 (SingletonMap (SymbolVar 3) (Sum 1)) (SingletonMap (BoundVar 0) (Sum 2))) 
    
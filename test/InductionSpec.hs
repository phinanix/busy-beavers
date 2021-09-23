module InductionSpec where

import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck

import Turing
import Count
import TuringExamples
import SimulateSkip
import Induction
import Skip

weird3Goal :: Skip Bit
weird3Goal = Skip
    -- 0 F (T, n) >T< F goes to 
    -- 0 (T, n+1) >T< F
    (Config (Phase 0) [(False, finiteCount 1), (True, newBoundVar 0)] True [(False, finiteCount 1)])
    (EndMiddle $ Config (Phase 0)
        [(True, finiteCount 1 <> newBoundVar 0)] True [(False, finiteCount 1)])
    (finiteCount 0) --obviously this is fake for now 
    False

checkerboardFalseGoal :: Skip Bit
checkerboardFalseGoal = Skip
    -- 0 >F< T (F, n) T goes to 
    -- 0 (T, n+3) >
    --true for n = 1 but not n = 2
    (Config (Phase 0) [] False [(True, finiteCount 1), (False, newBoundVar 0), (True, finiteCount 1)])
    (EndSide (Phase 0) R
        [(True, finiteCount 3 <> newBoundVar 0)])
    (finiteCount 0) --obviously this is fake for now 
    False

simple_sweeperGoal :: Skip Bit
simple_sweeperGoal = Skip
  --  F >T< (T, n) F goes to 
  -- >T< (T, n+1)  F 
  (Config (Phase 2) [(False, finiteCount 1)] True [(True, newBoundVar 0), (False, finiteCount 1)])
  (EndMiddle $ Config (Phase 2)
      [] True [(True, finiteCount 1 <> newBoundVar 0), (False, finiteCount 1)])
  (finiteCount 0) --obviously this is fake for now 
  False

c = finiteCount 
unsafeL1 = (\case
            [] -> error "lol"
            (x : xs) -> x :| xs)

spec :: Spec
spec = do
  describe "proveInductively" $ do
    it "proves a simple thing" $
      proveInductively 4 simple_sweeper (initBook simple_sweeper) simple_sweeperGoal (BoundVar 0)
      `shouldBe` Right (Induction (initBook simple_sweeper) 4)
    it "proves a counter machine counts" $
      proveInductively 4 weird3 (initBook weird3) weird3Goal (BoundVar 0)
      `shouldBe` Right (Induction (initBook weird3) 4)
    it "fails to pvoe a thing that is false" $
      proveInductively 20 checkerboardSweeper (initBook checkerboardSweeper) checkerboardFalseGoal
      (BoundVar 0) `shouldBe` Left "failed ind: machine stuck Phase 1 EndSide Phase 0 R [(True,Count 3 (fromList [(SymbolVar 4,Sum {getSum = 1})]) (fromList []))] ExpTape {left = [(True,NotInfinity Count 1 (fromList []) (fromList []))], point = True, right = [(False,NotInfinity Count 0 (fromList [(SymbolVar 4,Sum {getSum = 1})]) (fromList [])),(True,NotInfinity Count 1 (fromList []) (fromList []))]}"
  describe "replaceVarInSkip" $ do
    it "solves a simple case" $ do
      3 `shouldBe` 3
  describe "proveBySimulating" $ do 
    it "solves a simple case" $ do
      3 `shouldBe` 3
  describe "generalizeFromCounts" $ do 
    it "generalizes identical ints" $ do
      generalizeFromCounts (unsafeL1 $ replicate 5 (finiteCount 5, finiteCount 5)) 
        `shouldBe` Just (finiteCount 5, finiteCount 5)
    {- it "generalizes infinity" $ do 
      generalizeFromCounts (unsafeL1 $ replicate 5 (Infinity, Infinity))
        `shouldBe` Just (Infinity, Infinity) -}
    it "generalizes a basic additive function" $ do 
      generalizeFromCounts ((c 3, c 5) :| [(c 8, c 10), (c 2, c 4)]) 
        `shouldBe` Just (newBoundVar 0, newBoundVar 0 <> finiteCount 2)
    it "generalizes a subtractive function" $ do 
      generalizeFromCounts ((c 5, c 3) :| [(c 10, c 8), (c 4, c 2)]) 
        `shouldBe` Just (newBoundVar 0 <> finiteCount 2, newBoundVar 0)
    

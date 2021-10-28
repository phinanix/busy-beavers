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
import SimulationLoops
import Results 
import HaltProof
import HaltProof (HaltProof(BackwardSearch))
import TuringExamples (checkerboardSweeper)

weird3Goal :: Skip Bit
weird3Goal = Skip
    -- 0 F (T, n) >T< F goes to 
    -- 0 (T, n+1) >T< F
    (Config (Phase 0) [(False, finiteCount 1), (True, newBoundVar 0)] True [(False, finiteCount 1)])
    (EndMiddle $ Config (Phase 0)
        [(True, finiteCount 1 <> newBoundVar 0)] True [(False, finiteCount 1)])
    (finiteCount 0) --obviously this is fake for now 
    False
    Zero --obviously this is fake for now 

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
    Zero --obviously this is fake for now 

simple_sweeperGoal :: Skip Bit
simple_sweeperGoal = Skip
  --  F >T< (T, n) F goes to 
  -- >T< (T, n+1)  F 
  (Config (Phase 2) [(False, finiteCount 1)] True [(True, newBoundVar 0), (False, finiteCount 1)])
  (EndMiddle $ Config (Phase 2)
      [] True [(True, finiteCount 1 <> newBoundVar 0), (False, finiteCount 1)])
  (finiteCount 0) --obviously this is fake for now 
  False
  Zero --obviously this is fake for now 

c = finiteCount 

spec :: Spec
spec = do
  describe "transposeNE" $ do 
    it "works on a simple case" $ 
     transposeNE ([1,2] :| [[3,4],[5,6]]) `shouldBe` [1 :| [3,5], 2 :| [4,6]]
  describe "proveInductively" $ do
    it "proves a simple thing" $
      proveInductively 4 simple_sweeper (initBook simple_sweeper) simple_sweeperGoal (BoundVar 0)
      `shouldBe` Right (Induction (initBook simple_sweeper) 4)
    it "proves a counter machine counts" $
      proveInductively 4 weird3 (initBook weird3) weird3Goal (BoundVar 0)
      `shouldBe` Right (Induction (initBook weird3) 4)
    it "fails to pvoe a thing that is false" $
      proveInductively 20 checkerboardSweeper (initBook checkerboardSweeper) checkerboardFalseGoal
      (BoundVar 0) `shouldBe` Left "failed ind: machine stuck in phase:(Phase 1)\ngoal:phase: 0 (True, 3 + 1*a_4 ) |>\ncur tape:(T, 1) |>True<|(F, 0 + 1*a_4 ) (T, 1) "
  describe "replaceVarInSkip" $ do
    it "solves a simple case" $ do
      3 `shouldBe` 3
  describe "proveBySimulating" $ do 
    it "solves a simple case" $ do
      3 `shouldBe` 3
  describe "generalizeFromCounts" $ do 
    it "generalizes identical ints" $ do
      generalizeFromCounts (fromList $ replicate 5 (finiteCount 5, finiteCount 5)) 
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
    it "generalizes a multiplicative function" $ do -- 3x - 2
      generalizeFromCounts ((c 5, c 13) :| [(c 10, c 28), (c 2, c 4)]) 
        `shouldBe` Just (newBoundVar 0 <> finiteCount 2, nTimes 3 $ newBoundVar 0)
    it "fails to generalize when it isn't a pattern" $ do -- 3x - 2
      generalizeFromCounts ((c 5, c 13) :| [(c 10, c 42), (c 2, c 4)]) 
        `shouldBe` Nothing
    it "fails to generalize when the third doesn't match the first two " $ do -- 3x - 2
      generalizeFromCounts ((c 5, c 13) :| [(c 10, c 18), (c 2, c 4)]) 
        `shouldBe` Nothing
    --TODO, write basic tests for the 3 cases of generalizeFromInfCounts 
    --write several tests for guessInductionHypothesis    
  describe "guessInductionHypothesis" $ do
    it "guesses for a counting machine" $ do 
      -- at step 176, F (T, 5) F >F<
      -- at step 366, (T, 6)   F >F<
      --both phase 0
       makeIndGuess 1000 weird3 `shouldBe` Just (Skip 
        (Config (Phase 0) [(False, c 1), (True, Count 0 Empty (fromList [(BoundVar 0,Sum 1)])), (False, c 1)] False [])
        (EndMiddle (Config (Phase 0) [(True, Count 1 Empty (fromList [(BoundVar 0,Sum 1)])), (False, c 1)] False []))
        Empty
        False Zero) --this is of course only one reasonable guess, others would also be fine 
    it "guesses for a sweeper" $ do 
      -- at step 15, F >F< (T, 3)
      -- at step 24, >F< (T, 4)
      --both phase 0
      makeIndGuess 1000 simple_sweeper `shouldBe` Just (Skip 
        (Config (Phase 0) [(False, c 1)] False [(True, Count 0 Empty (fromList [(BoundVar 0, Sum 1)]))])
        (EndMiddle (Config (Phase 0) [] False [(True, Count 1 Empty (fromList [(BoundVar 0, Sum 1)]))]))
        Empty False Zero)
    it "guesses for a second sweeper" $ do 
      -- at step 6, F (T, 3) >F< F
      -- at step 15, (T, 5) >F<
      -- both phase 1 
      makeIndGuess 1000 checkerboardSweeper `shouldBe` Just (Skip 
        (Config (Phase 1) 
            [(False, c 1), (True, Count 0 Empty (fromList [(BoundVar 0, Sum 1)]))] False [(False, c 1)])
        (EndMiddle (Config (Phase 1) 
            
             [(True, Count 2 Empty (fromList [(BoundVar 0, Sum 1)]))] False []))
        Empty False Zero)
      
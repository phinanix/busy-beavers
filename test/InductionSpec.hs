module InductionSpec where

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
import TapeSymbol

checkerboardFalseGoal :: Skip Count Bit
checkerboardFalseGoal = Skip
    -- 0 >F< T (F, n) T goes to 
    -- 0 (T, n+3) >
    --true for n = 1 but not n = 2
    (Config (Phase 0) [] (Bit False) [(Bit True, finiteCount 1), (Bit False, newBoundVar 0), (Bit True, finiteCount 2)])
    (SkipStepped (Phase 0) $ Middle $ ExpTape [(Bit True, finiteCount 3 <> newBoundVar 0)] (Bit True) [])
    (finiteCount 0) --obviously this is fake for now 

simple_sweeperGoal :: Skip Count Bit
simple_sweeperGoal = Skip
  --  F >T< (T, n) F goes to 
  -- >T< (T, n+1)  F 
  (Config (Phase 2) [(Bit False, finiteCount 1)] (Bit True) [(Bit True, newBoundVar 0), (Bit False, finiteCount 1)])
  (SkipStepped (Phase 2) $ Middle $ ExpTape
      [] (Bit True) [(Bit True, finiteCount 1 <> newBoundVar 0), (Bit False, finiteCount 1)])
  (finiteCount 0) --obviously this is fake for now 

beforeReplace :: Config Count Bit
beforeReplace = Config (Phase 2) [(Bit False, symbolVarCount (SymbolVar 0) 1)] (Bit True) [(Bit True, One), (Bit False, One)]

afterReplace :: Config Count Bit
afterReplace = Config (Phase 2) [(Bit False, FinCount 5)] (Bit True) [(Bit True, One), (Bit False, One)]

c = finiteCount

assertPrettySkip :: (Pretty a1, Pretty a2) => Either Text a1 -> a2 -> Expectation
assertPrettySkip maybeSkip1 skip2 = (show . pretty <$> maybeSkip1) `shouldBe` Right (show (pretty skip2))

spec :: Spec
spec = do
  describe "transposeNE" $ do
    it "works on a simple case" $
     transposeNE ([1,2] :| [[3,4],[5,6]]) `shouldBe` [1 :| [3,5], 2 :| [4,6]]
  describe "proveInductively" $ do
    it "proves a simple thing" $
      proveInductively 20 simple_sweeper (initBookBit simple_sweeper) simple_sweeperGoal (BoundVar 0)
      `shouldBe` Right (Induction (initBookBit simple_sweeper) 20)
    xit "proves a counter machine counts" $
      proveInductively 20 weird3 (initBookBit weird3) weird3Goal (BoundVar 0)
      `shouldBe` Right (Induction (initBookBit weird3) 20)
    it "fails to pvoe a thing that is false" $
      proveInductively 20 checkerboardSweeper (initBookBit checkerboardSweeper) checkerboardFalseGoal
      (BoundVar 0) `shouldSatisfy` (has _Left)
    xit "proves a guess for the counter machine" $
      let goal = fromJust $ either (const Nothing) Just $ makeIndGuess 100 weird3 in
        proveInductively 20 weird3 (initBookBit weird3) goal (BoundVar 0) `shouldBe` Left ("", Nothing)
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
      --3x - 2 is not implemented by (x-2, 3x) !! that is 3x - 6 (eg 5-2 = 3, times 3 = 9 != 13)
      --(x-1, 3x + 1) should implement this eg 
      --  5-1 = 4 * 3 + 1 = 13
      --  10-1 = 9 * 3 + 1 = 28
      --  2-1 = 1 * 3 + 1 = 4
      generalizeFromCounts ((c 5, c 13) :| [(c 10, c 28), (c 2, c 4)])
        `shouldBe` Just (newBoundVar 0 <> finiteCount 1, nTimes 3 (newBoundVar 0) <> finiteCount 1)
    it "fails to generalize when it isn't a pattern" $ do
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
       makeIndGuess 1000 weird3 `assertPrettySkip` Skip
        (Config (Phase 2) [(Bit False, c 1)] (Bit False) [(Bit True, Count 0 Empty (fromList [(BoundVar 0,Sum 1)])), (Bit False, c 1)])
        (SkipStepped (Phase 2) $ Middle (ExpTape [] (Bit False) [(Bit True, Count 1 Empty (fromList [(BoundVar 0,Sum 1)])), (Bit False, c 1)]))
        Empty
        --this is of course only one reasonable guess, others would also be fine 
    it "guesses for a sweeper" $ do
      -- at step 15, F >F< (T, 3)
      -- at step 24, >F< (T, 4)
      --both phase 0
      makeIndGuess 1000 simple_sweeper `assertPrettySkip` Skip
        (Config (Phase 0) [(Bit False, c 1)] (Bit False) [(Bit True, Count 0 Empty (fromList [(BoundVar 0, Sum 1)])), (Bit False, c 1)])
        (SkipStepped (Phase 0) $ Middle (ExpTape [] (Bit False) [(Bit True, Count 1 Empty (fromList [(BoundVar 0, Sum 1)])), (Bit False, c 1)]))
        Empty
    it "guesses for a second sweeper" $ do
      -- at step 6, F (T, 3) >F< F
      -- at step 15, (T, 5) >F<
      -- both phase 1 
      makeIndGuess 1000 checkerboardSweeper `assertPrettySkip` Skip
        (Config (Phase 1)
            [(Bit True, Count 0 Empty (fromList [(BoundVar 0, Sum 1)])), (Bit False, c 1)] (Bit False) [(Bit False, c 1)])
        (SkipStepped (Phase 1) $ Middle (ExpTape
             [(Bit True, Count 2 Empty (fromList [(BoundVar 0, Sum 1)]))] (Bit False) []))
        Empty
  describe "replaceSymbolVarInConfig" $ do
    it "replaces in a simple example" $ do
      replaceSymbolVarInConfig True beforeReplace (SymbolVar 0) (FinCount 5) `shouldBe` afterReplace
  describe "calcCommonSig" $ do
    it "works on a real example" $
      calcCommonSig (Signature [Bit False] (Bit False) [Bit True,Bit False]) (Signature [] (Bit False) [Bit True,Bit False])
        `shouldBe` Just (True, False)
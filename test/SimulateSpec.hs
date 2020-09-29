module SimulateSpec where

--
import Relude
import Control.Lens
import Control.Lens.Extras

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)

import Util
import Count hiding (num)
import Turing
import ExpTape
import Skip
import Simulate

num = finiteCount

simpleTape :: ExpTape Bit Count
simpleTape = ExpTape
  ([(True, finiteCount 1)])
  (False, finiteCount 10, R)
  ([(True, finiteCount 3), (False, varCount 0)])

simpleSkip :: Skip Bit
simpleSkip = Skip
  (Config (Phase 0) [] (False, finiteCount 2, R) [])
  (Config (Phase 1) [(True, finiteCount 3)] (False, finiteCount 4, L) [(True, finiteCount 5)])

simpleResult :: ExpTape Bit Count
simpleResult = ExpTape
  ([(True, num 3), (False, num 8), (True, num 1)])
  (False, num 4, L)
  ([(True, num 8), (False, varCount 0)])


--
exampleSkip :: Skip Bit
exampleSkip = Skip
  (Config (Phase 0) [] (True, finiteCount 2, R) [(False, finiteCount 2), (True, finiteCount 1)])
  (Config (Phase 1) [(True, finiteCount 3)] (False, finiteCount 4, L) [(True, finiteCount 5)])

exampleTape :: ExpTape Bit Count
exampleTape = ExpTape
  ([(False, finiteCount 3), (True, finiteCount 1)])
  (True, finiteCount 8, R)
  ([(False, finiteCount 2), (True, finiteCount 3), (False, varCount 0)])

exampleResult :: ExpTape Bit Count
exampleResult = ExpTape
  ([(True, num 9), (False, num 3), (True, num 1)])
  (False, num 4, L)
  ([(True, num 7), (False, varCount 0)])

varSkip :: Skip Bit
varSkip = Skip
  (Config (Phase 0) [] (True, finiteCount 2, R) [(False, varCount 0), (True, finiteCount 1)])
  (Config (Phase 1) [(True, varCount 0)] (False, varCount 0, R) [] )

varTape :: ExpTape Bit Count
varTape = ExpTape
  ([(True, num 3)])
  (True, num 2, R)
  ([(False, num 8), (True, num 2)])

varResult :: ExpTape Bit Count
varResult = ExpTape
  ([(True, num 11)])
  (False, num 8, R)
  ([(True, num 1)])

skipTapeResultSpec skipEx phaseTapeIn@(phase_in, tapeEx) (phase_out, resultEx) = do
  it "matches the left half of the skip" $ do
    runEquationState (matchBitTape (skipEx^.start.ls) (left tapeEx))
      `shouldSatisfy`  is _Just
  it "matches the right half of the skip" $ do
    runEquationState (matchBitTape (skipEx^.start.rs) (right tapeEx))
      `shouldSatisfy` is _Just
  it "matches the point of the skip" $ do
    runEquationState (matchPoints (skipEx^.start.c_point) (point tapeEx))
      `shouldSatisfy` is _Just
  it "applies the skip" $ do
    applySkip simpleSkip phaseTapeIn
      `shouldBe` Just (Skipped phase_out resultEx)

spec :: Spec
spec = do
  describe "applySkip" $ do
    it "matches the left half of the skip" $ do
      runEquationState (matchBitTape (simpleSkip^.start.ls) (left simpleTape))
        `shouldBe` Just (NewTape (left simpleTape))
    it "matches the right half of the skip" $ do
      runEquationState (matchBitTape (simpleSkip^.start.rs) (right simpleTape))
        `shouldBe` Just (NewTape (right simpleTape))
    it "matches the point of the simple skip" $ do
      runEquationState (matchPoints (simpleSkip^.start.c_point) (point simpleTape))
        `shouldBe` Just (Lremains (False, num 8))
    it "applies a simple skip" $ do
      applySkip simpleSkip ((Phase 0), simpleTape)
        `shouldBe` Just (Skipped (Phase 1) simpleResult)
    it "passes the guard" $ do
      runEquationState (mfailGuard (exampleSkip^.start.ls == []) "ls not empty" >> matchBitTape (exampleSkip^.start.rs) (right exampleTape))
        `shouldSatisfy` is _Just
    it "passes the foo sham" $ do
      let thing = (,,) <$> pure id
            <*> pure (NewTape $ (True, num 6) : left exampleTape)
            <*> ((mfailGuard (exampleSkip^.start.ls == []) "ls not empty") >> (matchBitTape (exampleSkip^.start.rs) (right exampleTape)))
      (%~) _1 (const ()) <$> (runEquationState thing) `shouldSatisfy` is _Just
    it "foos correctly" $ do
      runEquationState ((\(x,
      y,z) -> (y,z)) <$> (foo exampleSkip ((Phase 0), exampleTape)))
        `shouldSatisfy` is _Just
    it "matches the point of the more complex skip" $ do
      runEquationState (matchPoints (exampleSkip^.start.c_point) (point exampleTape))
        `shouldBe` Just (Lremains (True, num 6))
    it "applies a more complex skip" $ do
      applySkip exampleSkip ((Phase 0), exampleTape)
        `shouldBe` Just (Skipped (Phase 1) exampleResult)

    --it seems to think varSkip and varTape's points have different symbols even though the next test that
    --tests that they match works
    describe "varExample" $ skipTapeResultSpec (varSkip) ((Phase 0), varTape) ((Phase 1), varResult)
    it "matches the point of the var" $ do
      runEquationState (matchPoints (varSkip^.start.c_point) (point varTape))
        `shouldBe` Just (PerfectP)

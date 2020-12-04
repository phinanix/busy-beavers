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

inum = finiteInfCount
num = finiteCount

simpleTape :: ExpTape Bit InfCount Location
simpleTape = ExpTape
  ([(True, inum 1)])
  (False, Side (inum 10) R)
  ([(True, inum 3), (False, newInfBoundVar 0)])

simpleSkip :: Skip Bit
simpleSkip = Skip
  (Config (Phase 0) [] (NotVar False, Side (num 2) R) [])
  (Config (Phase 1)
    [(NotVar True, num 3)]
    (NotVar False, Side (num 4) L)
    [(NotVar True, num 5)])
  (num 5) False

simpleResult :: ExpTape Bit InfCount Location
simpleResult = ExpTape
  ([(True, inum 3), (False, inum 8), (True, inum 1)])
  (False, Side (inum 4) L)
  ([(True, inum 8), (False, newInfBoundVar 0)])


--
exampleSkip :: Skip Bit
exampleSkip = Skip
  (Config (Phase 0) []
    (NotVar True, Side (num 2) R)
    [(NotVar False, num 2), (NotVar True, num 1)])
  (Config (Phase 1)
    [(NotVar True, num 3)]
    (NotVar False, Side (num 4) L)
    [(NotVar True, num 5)])
  (num 10) False

exampleTape :: ExpTape Bit InfCount Location
exampleTape = ExpTape
  ([(False, inum 3), (True, inum 1)])
  (True, Side (inum 8) R)
  ([(False, inum 2), (True, inum 3), (False, newInfBoundVar 0)])

exampleResult :: ExpTape Bit InfCount Location
exampleResult = ExpTape
  ([(True, inum 9), (False, inum 3), (True, inum 1)])
  (False, Side (inum 4) L)
  ([(True, inum 7), (False, newInfBoundVar 0)])

varSkip :: Skip Bit
varSkip = Skip
  (Config (Phase 0) []
    (NotVar True, Side (num 2) R)
    [(NotVar False, newBoundVar 0), (NotVar True, num 1)])
  (Config (Phase 1)
    [(NotVar True, newBoundVar 0)]
    (NotVar False, Side (newBoundVar 0) R) [] )
  (Count 8 Empty (fromList [(BoundVar 0, Sum 3)]))
  False

varTape :: ExpTape Bit InfCount Location
varTape = ExpTape
  ([(True, inum 3)])
  (True, Side (inum 2) R)
  ([(False, inum 8), (True, inum 2)])

varResult :: ExpTape Bit InfCount Location
varResult = ExpTape
  ([(True, inum 11)])
  (False, Side (inum 8) R)
  ([(True, inum 1)])

skipTapeResultSpec skipEx phaseTapeIn@(phase_in, tapeEx) (phase_out, resultEx) = do
  it "matches the left half of the skip" $ do
    runEquations (matchBitTape (skipEx^.start.ls) (left tapeEx))
      `shouldSatisfy`  is _Just
  it "matches the right half of the skip" $ do
    runEquations (matchBitTape (skipEx^.start.rs) (right tapeEx))
      `shouldSatisfy` is _Just
  it "matches the point of the skip" $ do
    runEquations (matchPoints (skipEx^.start.c_point) (point tapeEx))
      `shouldSatisfy` is _Just
  it "applies the skip" $ do
    applySkip skipEx phaseTapeIn
      `shouldBe` Just (Skipped phase_out resultEx)

spec :: Spec
spec = do
  describe "applySkip" $ do
    it "matches the left half of the skip" $ do
      getEquations (matchBitTape (simpleSkip^.start.ls) (left simpleTape))
        `shouldBe` Just (NewTape (left simpleTape))
    it "matches the right half of the skip" $ do
      getEquations (matchBitTape (simpleSkip^.start.rs) (right simpleTape))
        `shouldBe` Just (NewTape (right simpleTape))
    it "matches the point of the simple skip" $ do
      getEquations (matchPoints (simpleSkip^.start.c_point) (point simpleTape))
        `shouldBe` Just (Lremains (False, inum 8))
    it "applies a simple skip" $ do
      applySkip simpleSkip ((Phase 0), simpleTape)
        `shouldBe` Just (Skipped (Phase 1) simpleResult)
    it "passes the guard" $ do
      runEquations (mfailGuard (exampleSkip^.start.ls == []) "ls not empty" >> matchBitTape (exampleSkip^.start.rs) (right exampleTape))
        `shouldSatisfy` is _Just
    it "matches the point of the more complex skip" $ do
      getEquations (matchPoints (exampleSkip^.start.c_point) (point exampleTape))
        `shouldBe` Just (Lremains (True, inum 6))
    it "applies a more complex skip" $ do
      applySkip exampleSkip ((Phase 0), exampleTape)
        `shouldBe` Just (Skipped (Phase 1) exampleResult)

    --it seems to think varSkip and varTape's points have different symbols even though the next test that
    --tests that they match works
    describe "varExample" $ skipTapeResultSpec (varSkip) ((Phase 0), varTape) ((Phase 1), varResult)
    it "matches the point of the var" $ do
      getEquations (matchPoints (varSkip^.start.c_point) (point varTape))
        `shouldBe` Just (PerfectP)

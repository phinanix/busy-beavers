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
import SimulateSkip

inum = finiteInfCount
num = finiteCount

simpleTape :: ExpTape Bit InfCount
simpleTape = ExpTape
  [(False, inum 9), (True, inum 1)]
  False
  [(True, inum 3), (False, newInfBoundVar 0)]

simpleSkip :: Skip Bit
simpleSkip = Skip
  (Config (Phase 0) [(False, num 1)] False [])
  (EndMiddle (Config (Phase 1)
    [(True, num 3)]
    False
    [(False, num 3), (True, num 5)]))
  (num 5) False

simpleResult :: ExpTape Bit InfCount
simpleResult = ExpTape
  [(True, inum 3), (False, inum 8), (True, inum 1)]
  False
  [(False, inum 3), (True, inum 8), (False, newInfBoundVar 0)]


--
exampleSkip :: Skip Bit
exampleSkip = Skip
  (Config (Phase 0) [(True, One)]
    True
    [(False, num 2), (True, num 1)])
  (EndMiddle (Config (Phase 1)
    [(True, num 3)]
    False
    [(False, num 3), (True, num 5)]))
  (num 10) False

exampleTape :: ExpTape Bit InfCount
exampleTape = ExpTape
  [(True, inum 7), (False, inum 3), (True, inum 1)]
  True
  [(False, inum 2), (True, inum 3), (False, newInfBoundVar 0)]

exampleResult :: ExpTape Bit InfCount
exampleResult = ExpTape
  [(True, inum 9), (False, inum 3), (True, inum 1)]
  False
  [(False, inum 3), (True, inum 7), (False, newInfBoundVar 0)]

varSkip :: Skip Bit
varSkip = Skip
  (Config (Phase 0) [(True, One)]
    True
    [(False, One <> newBoundVar 0), (True, num 1)])
  (EndMiddle (Config (Phase 1)
    [(False, newBoundVar 0), (True, One <> newBoundVar 0)]
    False []))
  (Count 11 Empty (fromList [(BoundVar 0, Sum 3)]))
  False

varTape :: ExpTape Bit InfCount
varTape = ExpTape
  [(True, IOne), (True, inum 3)]
  True
  [(False, inum 8), (True, inum 2)]

varResult :: ExpTape Bit InfCount
varResult = ExpTape
  [(False, inum 7), (True, inum 11)]
  False
  [(True, inum 1)]

spec :: Spec
spec =
  describe "applySkip" $ do
  it "matches the left half of the skip" $
    getEquations (matchTape (simpleSkip^.start.ls) (left simpleTape))
    `shouldBe` Just (TapeLeft $ (False, inum 8) :| [(True, inum 1)])
  it "matches the right half of the skip" $
    getEquations (matchTape (simpleSkip^.start.rs) (right simpleTape))
    `shouldBe` Just (TapeLeft $ fromList (right simpleTape))
  -- it "matches the point of the simple skip" $ do
  --   getEquations (matchPoints (simpleSkip^.start.c_point) (point simpleTape))
  --     `shouldBe` Just (Lremains (False, inum 8))
  it "applies a simple skip" $
    applySkip simpleSkip (Phase 0, simpleTape)
    `shouldBe` Just (Skipped (NotInfinity $ num 5) (Phase 1) simpleResult)
  -- it "matches the point of the more complex skip" $ do
  --   getEquations (matchPoints (exampleSkip^.start.c_point) (point exampleTape))
  --     `shouldBe` Just (Lremains (True, inum 6))
  it "applies a more complex skip" $
    applySkip exampleSkip (Phase 0, exampleTape)
    `shouldBe` Just (Skipped (NotInfinity $ num 10) (Phase 1) exampleResult)
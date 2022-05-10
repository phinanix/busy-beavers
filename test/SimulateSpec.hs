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
import TuringExamples
import ExpTape
import Results
import Skip
import Simulate ()
import SimulateSkip ( applySkip, PartialStepResult(..) )

inum = finiteInfCount
num = finiteCount

simpleTape :: ExpTape Bit InfCount
simpleTape = ExpTape
  [(Bit False, inum 11), (Bit True, inum 1)]
  (Bit False)
  [(Bit True, inum 3), (Bit False, newInfBoundVar 0)]

simpleSkip :: Skip Count Bit
-- (F, 11) >F< 
-- (T, 3) >F< (F,3) (T,5)
-- huh, not actually a legal skip
simpleSkip = Skip
  (Config (Phase 0) [(Bit False, num 11)] (Bit False) [])
  (SkipStepped (Phase 1) $ Middle (ExpTape
    [(Bit True, num 3)]
    (Bit False)
    [(Bit False, num 3), (Bit True, num 5)]))
  (num 5)

simpleResult :: ExpTape Bit InfCount
simpleResult = ExpTape
  [(Bit True, inum 4)]
  (Bit False)
  [(Bit False, inum 3), (Bit True, inum 8), (Bit False, newInfBoundVar 0)]


exampleSkip :: Skip Count Bit
-- (T, 1) T (F, 2) (T, 1)
-- (T, 3) F (F, 1)
exampleSkip = Skip
  (Config (Phase 0) [(Bit True, One)]
    (Bit True)
    [(Bit False, num 2), (Bit True, num 1)])
  (SkipStepped (Phase 1) $ Middle (ExpTape
    [(Bit True, num 3)]
    (Bit False)
    [(Bit False, num 1)]))
  (num 10)

exampleTape :: ExpTape Bit InfCount
exampleTape = ExpTape
  [(Bit True, inum 7), (Bit False, inum 3), (Bit True, inum 1)]
  (Bit True)
  [(Bit False, inum 2), (Bit True, inum 3), (Bit False, newInfBoundVar 0)]

exampleResult :: ExpTape Bit InfCount
exampleResult = ExpTape
  [(Bit True, inum 9), (Bit False, inum 3), (Bit True, inum 1)]
  (Bit False)
  [(Bit False, inum 1), (Bit True, inum 2), (Bit False, newInfBoundVar 0)]

varSkip :: Skip Count Bit
varSkip = Skip
  (Config (Phase 0) [(Bit True, One)]
    (Bit True)
    [(Bit False, One <> newBoundVar 0), (Bit True, num 1)])
  (SkipStepped (Phase 1) $ Middle (ExpTape
    [(Bit False, newBoundVar 0), (Bit True, One <> newBoundVar 0)]
    (Bit False) []))
  (Count 11 Empty (fromList [(BoundVar 0, Sum 3)]))


varTape :: ExpTape Bit InfCount
varTape = ExpTape
  [(Bit True, IOne), (Bit True, inum 3)]
  (Bit True)
  [(Bit False, inum 8), (Bit True, inum 2)]

varResult :: ExpTape Bit InfCount
varResult = ExpTape
  [(Bit False, inum 7), (Bit True, inum 11)]
  (Bit False)
  [(Bit True, inum 1)]

getContinueSteps :: SimResult s a -> Maybe Steps
getContinueSteps = \case
  Continue steps _ _ _ -> Just steps
  _ -> Nothing

spec :: Spec
spec = do
  describe "applySkip" $ do
    it "matches the left half of the skip" $
      getEquations (matchTape (simpleSkip^.start.ls) (left simpleTape))
      `shouldBe` Just (TapeLeft $ (Bit True, inum 1) :| [])
    it "matches the right half of the skip" $
      getEquations (matchTape (simpleSkip^.start.rs) (right simpleTape))
      `shouldBe` Just (TapeLeft $ fromList (right simpleTape))
    it "applies a simple skip" $
      applySkip simpleSkip (Phase 0, simpleTape)
      `shouldBe` Just (Stepped 
          (NotInfinity $ num 5) 
          (Phase 1) 
          simpleResult 
          simpleSkip
          (Just $ -8) 
          (Just $ ReadShift (-11) 0 (-8)))
    it "applies a more complex skip" $
      applySkip exampleSkip (Phase 0, exampleTape)
      `shouldBe` Just (Stepped 
          (NotInfinity $ num 10) 
          (Phase 1) 
          exampleResult 
          exampleSkip 
          (Just 2)
          (Just $ ReadShift (-1) 3 2))

  -- describe "simulateOneMachine" $ do
  --   it "stops after the specified number of tests" $
  --     Simulate.simulateOneMachine 4 bb3 initSimState ^? _Right . _Continue . _1 
  --       `shouldBe` Just 4

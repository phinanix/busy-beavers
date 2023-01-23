module SimulateSkipSpec where 

import Relude 
import Control.Lens
import Control.Lens.Extras

import Test.Hspec
import Test.QuickCheck

import Turing 
import TuringExamples
import Results  
import Count
import Tape 
import ExpTape
import Skip
import Simulate  
import SimulateSkip
import SimulateTwoBit
import ShortNames

--blindly assumes the Turing machine here is a total one 
-- simulateBasicAndSkip :: Int -> Turing -> (SimResult Bit (Tape Bit), SimResult Bit SkipTape)
-- simulateBasicAndSkip limit t = (normalRes, skipRes) where 
--     normalRes = case Simulate.simulateOneMachine limit t initSimState of 
--         Left e -> error $ show e <> " was not a known edge simulateBasicAndSkip"
--         Right res -> res 
--     skipRes = case SimulateSkip.simulateOneMachine limit t (initSkipState t) of 
--         (_, Left e) -> error $ show e <> " was not a known edge simulateBasicAndSkip 2"
--         (_, Right res) -> res

-- simulateBasicAndGlue :: Int -> Turing -> (SimResult (Tape Bit), SimResult SkipTape)
-- simulateBasicAndGlue limit t = (normalRes, skipRes) where 
--   normalRes = case Simulate.simulateOneMachine limit t initSimState of 
--           Left e -> error $ show e <> " was not a known edge simulateBasicAndGlue"
--           Right res -> res 
--   skipRes = case SimulateSkip.simulateOneMachineByGluing limit t (initSkipState t) of 
--     (_, _, Left e) -> error $ show e <> " was not a known edge simulateBasicAndGlue 2"
--     (_, _, Right res) -> res 

-- twoThingsSimulatesSame :: SimResult Bit (Tape Bit) -> SimResult Bit SkipTape -> Expectation 
-- twoThingsSimulatesSame normalRes skipRes = if normalSteps == skipSteps 
--         then normalRes `shouldBe` expTapeToTape <$> skipRes 
--         else pure () --skips don't always stop right at the limit
--         where 
--         normalSteps = normalRes ^? _Continue . _1 
--         skipSteps = skipRes ^? _Continue . _1 

-- simulatesSameForAll :: (Int -> Turing -> (SimResult Bit (Tape Bit), SimResult Bit SkipTape)) 
--   -> Int -> Turing -> Expectation 
-- simulatesSameForAll func limit t = for_ [0.. limit] 
--   (\i -> uncurry twoThingsSimulatesSame $ func i t)

-- the point of this function is given a machine plus a skip we expect to hold for that machine, 
-- to check that skip in fact holds for the machine by using naive simulation 
skipIsCorrect :: Int -> Turing -> Skip Count Bit -> Expectation 
skipIsCorrect limit t skip = undefined 

{-
we were applying: in 100 steps we turn
phase: 3  (F, 1) (T, 1 + 1*x_0 ) |>T<|
into:
phase: 1  (T, 1) |>F<|(F, 0 + 1*x_0 ) (T, 1)
 displacement of: Zero

to tape:
(F, inf) (T, 1) |>T<|(T, 7) (F, inf)

resulting in:
(F, inf) (T, 1) |>F<|(F, 0) (T, 8) (F, inf)
the above is wrong, because that skip does not apply in this situation, but at the time of 
  writing this comment (29 Dec 2021) the code did apply the above skip resulting in an exptape
  which does not satisfy its no-zeros invariant
-}

{- in 100 steps we turn
phase: 3  (F, 1) (T, 1 + 1*x_0 ) |>T<|
into:
phase: 1  (T, 1) |>F<|(F, 0 + 1*x_0 ) (T, 1)
 displacement of: Zero -}
skipEx :: Skip Count Bit
skipEx = Skip 
  (Config (Phase 3) [(Bit True, One <> boundVarCount (BoundVar 0) 1)] (Bit True) [])
  (SkipStepped  (Phase 1) $ Middle $ ExpTape [(Bit True, One)] (Bit False) [(Bit False, boundVarCount (BoundVar 0) 1), (Bit True, One)])
  Empty
--(F, inf) (T, 1) |>T<|(T, 7) (F, inf)
tapeEx :: (Phase, ExpTape Bit InfCount)
tapeEx = (Phase 3,
  ExpTape [(Bit True, NotInfinity One), (Bit False, Infinity)] 
    (Bit True) 
    [(Bit True, NotInfinity $ finiteCount 7), (Bit False, Infinity)]
  )

spec :: Spec 
spec = do
  describe "applySkip" $ do 
    it "does not apply a skip which would set a variable to zero" $ do 
      applySkip undefined skipEx tapeEx `shouldBe` Nothing 
  -- the goal of this test is to make sure that simulating the machine with skips outputs the same thing 
  -- as simulating a machine without skips
  -- describe "simulateWithSkips" $ do 
  --   it "produces the same results as normal simulation" $ 
  --     simulatesSameForAll simulateBasicAndSkip 40 bb3
  -- describe "simulateByGluing" $ do 
  --   it "produces the same results as normal simulation" $ 
  --     simulatesSameForAll simulateBasicAndGlue 40 bb3
    it "applies a skip which it didn't and I am confused about why (regression test-ish)" $ do 
      {-
      in 50 steps we turn
      phase: 0  (|TT|, 0 + 1*x_1 ) (|FT|, 2) |>|FT|<|(|FT|, 0 + 1*x_0 ) (|FF|, 0 + 1*x_1 )
      into:
      phase: 0(|FT|, 2) |>|FT|<|(|FT|, 0 + 1*x_0 2*x_1 )

      phase: 0  (|FF|, 1) (|TT|, 0 + 1*x_0 ) (|FT|, 2) |>|FT|<|(|FT|, 1) (|FF|, 1 + 1*x_0 )
      -}
      let ff = TwoBit (Bit False) (Bit False)
          ft = TwoBit (Bit False) (Bit True)
          tt = TwoBit (Bit True) (Bit True)
          c = FinCount
          ci = NotInfinity . FinCount 
          bv x = boundVarCount (BoundVar x)
          bvi x = boundVarInfCount (BoundVar x)
          skipEx2 = Skip (Config (Phase 0) [(ft, c 2), (tt, bv 1 1)] ft [(ft, bv 0 1), (ff, bv 1 1)]) 
            (SkipStepped (Phase 0) (Middle (ExpTape [] ft []))) 
            (c 50)
          tapeEx2 = (Phase 0, ExpTape [(ft, ci 2), (tt, bvi 0 1), (ff, ci 1)] 
                                      ft [(ft, ci 1), (ff, ci 1 <> bvi 0 1)])                     
      applySkip undefined skipEx2 tapeEx2 `shouldSatisfy` has _Just
  describe "matchTwoTapes" $ do
    it "applies a skip when a var is sent to two things" $ do 
      {-
      matchTape [(F, x), (T, 1), (F, x)] [(F, 2), (T, 1), (F, 3)] 
      the answer should be (x -> 2) [(F, 1)]
      -}
      let bv x = boundVarCount (BoundVar x)
          c = FinCount
          ci = NotInfinity . FinCount 
          tape1 = [(Bit False, bv 1 1), (Bit True, c 1), (Bit False, bv 1 1)]
          tape2 = [(Bit False, ci 2), (Bit True, ci 1), (Bit False, ci 3)]
          ansTape = (Bit False, ci 1) :| []
      getEquations (matchTwoTapes (tape1, tape2) ([], [])) `shouldBe` Just (TapeLeft ansTape, Perfect)
  describe "getLen" $ do 
    it "gets a simple len" $ 
      getLen Empty [(tt, One <> One)] `shouldBe` Just 2 
    -- it "fails to get a len it got wrong before" $ 
    --   getLen EMpty 
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

--blindly assumes the Turing machine here is a total one 
simulateBasicAndSkip :: Int -> Turing -> (SimResult Tape, SimResult SkipTape)
simulateBasicAndSkip limit t = (normalRes, skipRes) where 
    normalRes = case Simulate.simulateOneMachine limit t initSimState of 
        Left e -> error $ show e <> " was not a known edge simulateBasicAndSkip"
        Right res -> res 
    skipRes = case SimulateSkip.simulateOneMachine limit t (initSkipState t) of 
        (_, Left e) -> error $ show e <> " was not a known edge simulateBasicAndSkip 2"
        (_, Right res) -> res

-- simulateBasicAndGlue :: Int -> Turing -> (SimResult Tape, SimResult SkipTape)
-- simulateBasicAndGlue limit t = (normalRes, skipRes) where 
--   normalRes = case Simulate.simulateOneMachine limit t initSimState of 
--           Left e -> error $ show e <> " was not a known edge simulateBasicAndGlue"
--           Right res -> res 
--   skipRes = case SimulateSkip.simulateOneMachineByGluing limit t (initSkipState t) of 
--     (_, _, Left e) -> error $ show e <> " was not a known edge simulateBasicAndGlue 2"
--     (_, _, Right res) -> res 

twoThingsSimulatesSame :: SimResult Tape -> SimResult SkipTape -> Expectation 
twoThingsSimulatesSame normalRes skipRes = if normalSteps == skipSteps 
        then normalRes `shouldBe` expTapeToTape <$> skipRes 
        else pure () --skips don't always stop right at the limit
        where 
        normalSteps = normalRes ^? _Continue . _1 
        skipSteps = skipRes ^? _Continue . _1 

simulatesSameForAll :: (Int -> Turing -> (SimResult Tape, SimResult SkipTape)) -> Int -> Turing -> Expectation 
simulatesSameForAll func limit t = for_ [0.. limit] 
  (\i -> uncurry twoThingsSimulatesSame $ func i t)

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
skipEx = undefined
--(F, inf) (T, 1) |>T<|(T, 7) (F, inf)
tapeEx = (Phase 3,
  ExpTape [(Bit True, NotInfinity One), (Bit False, Infinity)] 
    (Bit True) 
    [(Bit True, NotInfinity $ finiteCount 7), (Bit False, Infinity)]
  )

spec :: Spec 
spec = do
  describe "applySkip" $ do 
    it "does not apply a skip which would set a variable to zero" $ do 
      applySkip skipEx tapeEx `shouldBe` Nothing 
  -- the goal of this test is to make sure that simulating the machine with skips outputs the same thing 
  -- as simulating a machine without skips
  -- describe "simulateWithSkips" $ do 
  --   it "produces the same results as normal simulation" $ 
  --     simulatesSameForAll simulateBasicAndSkip 40 bb3
  -- describe "simulateByGluing" $ do 
  --   it "produces the same results as normal simulation" $ 
  --     simulatesSameForAll simulateBasicAndGlue 40 bb3
  pure ()
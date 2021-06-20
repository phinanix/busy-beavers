module SimulateSkipSpec where 

import Relude 
import Control.Lens
import Control.Lens.Extras

import Test.Hspec
import Test.QuickCheck

import Turing 
import TuringExamples
import Results  
import Tape 
import ExpTape
import Skip
import Simulate  
import SimulateSkip

--blindly assumes the Turing machine here is a total one 
simulateWithBoth :: Int -> Turing -> (SimResult Tape, SimResult SkipTape)
simulateWithBoth limit t = (normalRes, skipRes) where 
    normalRes = case Simulate.simulateOneMachine limit t initSimState of 
        Left e -> error $ show e <> " was not a known edge simulateWithBoth"
        Right res -> res 
    skipRes = case SimulateSkip.simulateOneMachine limit t (initSkipState t) of 
        (_, Left e) -> error $ show e <> " was not a known edge simulateWithBoth 2"
        (_, Right res) -> res

simulatesSame :: Int -> Turing -> Expectation 
simulatesSame limit t = case simulateWithBoth limit t of 
    (normalRes, skipRes) -> if normalSteps == skipSteps 
        then normalRes `shouldBe` expTapeToTape <$> skipRes 
        else pure () --skips don't always stop right at the limit
        where 
        normalSteps = normalRes ^? _Continue . _1 
        skipSteps = skipRes ^? _Continue . _1 

simulatesSameForAll :: Int -> Turing -> Expectation 
simulatesSameForAll limit t = for_ [0.. limit] (\i -> simulatesSame i t)

-- the point of this function is given a machine plus a skip we expect to hold for that machine, 
-- to check that skip in fact holds for the machine by using naive simulation 
skipIsCorrect :: Int -> Turing -> Skip Bit -> Expectation 
skipIsCorrect limit t skip = undefined 

spec :: Spec 
spec = 
  -- the goal of this test is to make sure that simulating the machine with skips outputs the same thing 
  -- as simulating a machine without skips
  describe "simulateWithSkips" $ do 
    it "produces the same results as normal simulation" $ 
      simulatesSameForAll 40 bb3
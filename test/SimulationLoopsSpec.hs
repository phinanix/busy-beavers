module SimulationLoopsSpec where

import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck

import Turing
import Count
import ExpTape 
import Results 
import Skip 
import SimulateSkip
import SimulationLoops 

import HaltProof
import TuringExamples
import ShortNames 
import Util 

test :: InfCount 
test = NotInfinity (c 2)

spec :: Spec 
spec = do 
  describe "attemptEndOfTapeGlueProof" $ do 
    it "proves a simple goes forever machine" $ do 
      fst (loopForEndOfTapeGlue 100 goesLeftForever) `shouldBe` ContinueForever (OffToInfinityN 2 L)
    it "does not prove a machine that doesn't halt in this way" $ do 
      fst (loopForEndOfTapeGlue 100 weird3) `shouldBe`  
        --this is the wrong stepcount but my program producing incorrect 
        --stepcounts is a known issue
        Continue 885
          (Phase 2) 
          (ExpTape 
            [(Bit True,NotInfinity (Count 2 (fromList []) (fromList []))),(Bit False,NotInfinity (Count 1 (fromList []) (fromList []))),(Bit True,NotInfinity (Count 1 (fromList []) (fromList []))),(Bit False,Infinity)] 
            (Bit False)
            [(Bit True,NotInfinity (Count 1 (fromList []) (fromList []))),(Bit False,Infinity)]) (-2)

  describe "skipRunsForeverIfConsumesLiveTape" $ do 
    it "says the example runs forever" $ do 
      {-
      Right: in 0 steps we turn
      phase: 2  (|FF|, 1) |>|FT|<|(|FT|, 0 + 1*x_0 ) (|FF|, 4 + 1*x_0 )
      into:
      phase: 2|>|FT|<|(|FT|, 5 + 2*x_0 )
      -}
      let s = Skip (Config (ph 2) [(f, c 1)] t [(t, bv 0 1), (f, c 4 <> bv 0 1)])
            (SkipStepped (ph 2) (Middle (ExpTape [] t [(t, c 5 <> bv 0 2)])))
            Empty 
      skipRunsForeverIfConsumesLiveTape s `shouldBe` True 
    it "says a made up example doesn't run forever" $ do 
      {-
      Right: in 0 steps we turn
      phase: 2  (|TF|, 1) |>|FT|<|(|FT|, 0 + 1*x_0 ) (|FF|, 4 + 1*x_0 )
      into:
      phase: 2|>|FT|<|(|FT|, 5 + 2*x_0 )
      -}
      let s = Skip (Config (ph 2) [(t, c 1)] t [(t, bv 0 1), (f, c 4 <> bv 0 1)])
            (SkipStepped (ph 2) (Middle (ExpTape [] t [(t, c 5 <> bv 0 2)])))
            Empty 
      skipRunsForeverIfConsumesLiveTape s `shouldBe` False
    it "says another example runs forever" $ do 
      {-
      phase: 3  (F, 3) |>F<|(T, 0 + 1*x_0 ) (F, 7 + 2*x_0 )
      into:
      phase: 3(F, 1) |>F<|(T, 9 + 3*x_0 )
      -}
      let s = Skip (Config (ph 3) [(f, c 3)] f [(t, bv 0 1), (f, bv 0 2 <> c 7)])
            (SkipStepped (ph 3) (Middle (ExpTape [(f, c 1)] f [(t, bv 0 3 <> c 9)])))
            Empty
      trace ("yelling about skip: " <> showP s) skipRunsForeverIfConsumesLiveTape s `shouldBe` True 
module TapeSymbolSpec where

import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck


import Util
import Count
import Turing
import Skip
import Notation (dispTuring)
import TapeSymbol
import SimulateTwoBit
import ExpTape


spec :: Spec
spec = do
  describe "chainArbitrary" $ do
    it "chains something it previously didn't" $ do
      {-
        in 0 steps we turn
        phase: 0  (|FF|, 1) |>|FT|<|(|FT|, 0 + 1*x_0 ) (|FF|, 2)
        into:
        phase: 0|>|FT|<|(|FT|, 2 + 1*x_0 ) (|FF|, 1)
      should chain to 
        in 0 steps we turn
        phase: 0  (|FF|, 1*x_1) |>|FT|<|(|FT|, 0 + 1*x_0 ) (|FF|, 1 + 1*x_1)
        into:
        phase: 0|>|FT|<|(|FT|, 1*x_0 + 2*x_1 ) (|FF|, 1)

        -}
      chainArbitrary (Skip
        (Config (Phase 0) 
          [(TwoBit (Bit False) (Bit False), One)] 
          (TwoBit (Bit False) (Bit True)) 
          [(TwoBit (Bit False) (Bit True), boundVarCount (BoundVar 0) 1), 
              (TwoBit (Bit False) (Bit False), FinCount 2)])
        (SkipStepped (Phase 0) (Middle (ExpTape 
          [] 
          (TwoBit (Bit False) (Bit True)) 
          [(TwoBit (Bit False) (Bit True), FinCount 2 <> boundVarCount (BoundVar 0) 1), 
              (TwoBit (Bit False) (Bit False), One)])))
        Empty
        )
        `shouldBe` Right (Skip
        (Config (Phase 0) 
          [(TwoBit (Bit False) (Bit False), boundVarCount (BoundVar 1) 1)] 
          (TwoBit (Bit False) (Bit True)) 
          [(TwoBit (Bit False) (Bit True), boundVarCount (BoundVar 0) 1), 
              (TwoBit (Bit False) (Bit False), One <> boundVarCount (BoundVar 1) 1)])
        (SkipStepped (Phase 0) (Middle (ExpTape 
          [] 
          (TwoBit (Bit False) (Bit True)) 
          [(TwoBit (Bit False) (Bit True), boundVarCount (BoundVar 0) 1 <> boundVarCount (BoundVar 1) 2), 
              (TwoBit (Bit False) (Bit False), One)])))
        (FinCount 50)
        )
    it "chains correctly something it previously didn't" $ do 
      {-
      *** Exception: chainArb bug, inp: in 0 steps we turn
phase: 0  (F, 2) (T, 0 + 1*x_0 ) |>F<|(T, 1)
into:
phase: 0(T, 1 + 1*x_0 ) |>F<|(T, 2)


incorrect output:in 50 steps we turn
phase: 0  (F, 0 + 2*x_1 ) (T, 0 + 1*x_0 ) |>F<|(T, 1 + 1*x_1 )
into:
phase: 0(T, 0 + 1*x_0 1*x_1 ) |>F<|(T, 1)
      -}
      chainArbitrary (Skip 
        (Config (Phase 0)
        [(Bit True, boundVarCount (BoundVar 0) 1), (Bit False, One <> One)]
        (Bit False) 
        [(Bit True, One)]
        )
        (SkipStepped (Phase 0) (Middle (ExpTape 
        [(Bit True, One <> boundVarCount (BoundVar 0) 1)] 
        (Bit False)
        [(Bit True, One <> One)])))
        Empty 
       ) `shouldBe` Right (Skip 
        (Config (Phase 0)
        [(Bit True, boundVarCount (BoundVar 0) 1), (Bit False, boundVarCount (BoundVar 1) 2)]
        (Bit False) 
        [(Bit True, One)]
        )
        (SkipStepped (Phase 0) (Middle (ExpTape 
        [(Bit True, boundVarCount (BoundVar 0) 1 <> boundVarCount (BoundVar 1) 1)] 
        (Bit False)
        [(Bit True, One <> boundVarCount (BoundVar 1) 1)])))
        Empty 
       )
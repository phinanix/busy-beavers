module AbstractInterpretationSpec where


import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)
import qualified Data.Vector.Fixed as V

import Count hiding (num)
import Turing
import ExpTape
import Skip
import AbstractInterpretation
import TuringExamples
import TapeSymbol


spec :: Spec
spec = do
  describe "nearHeadGetNextConfigs" $ do
    let
      --TR1FR3TR2___FL0TR0TL2TR3 
      m = tailEatingDragonFast
      book = mapBook Base $ initBook @Bit m
    it "steps a machine forward" $ let
      --0F -> TR1
      conf = Just (Phase 0, ExpTape [(Base (Bit False), NotInfinity One)] (Base (Bit False))
        [(Base (Bit False), NotInfinity One)])
      ans = Just (Phase 1, ExpTape [(Base (Bit True), NotInfinity One), (Base (Bit False), NotInfinity One)]
        (Base (Bit False)) [])
      in
      nearHeadGetNextConfigs 6 m book conf `shouldBe` [ans]
    it "branches the world" $ let
      --1F -> TR2
      conf = Just (Phase 1, ExpTape [(Base (Bit False), NotInfinity One)] (Base (Bit False))
        [(MultipleAny, NotInfinity One)])
      ansHole b = Just (Phase 2, ExpTape [(Base (Bit True), NotInfinity One), (Base (Bit False), NotInfinity One)]
        (Base b) [(MultipleAny, NotInfinity One)])
      in
      nearHeadGetNextConfigs 6 m book conf `shouldBe` ansHole <$> [Bit False, Bit True]
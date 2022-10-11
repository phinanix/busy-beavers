module RunnerSpec where


import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)
import qualified Data.Vector.Fixed as V

import Turing
import TuringExamples
import Runner

spec :: Spec
spec = do
  describe "intTo3Bit" $ do
    it "encodes 0" $
      intTo3Bit 0 `shouldBe` [False, False, False]
    it "encodes 3" $
      intTo3Bit 3 `shouldBe` [False, True, True]
  describe "threeBitsToInt" $ do 
    it "decodes 1" $
      threeBitsToInt (False, False, True) `shouldBe` 1 
  let randomTrans = Just $ Step (Phase 1) (Bit True) R
  describe "pack and unpack bits" $ do 
    it "decode encode law" $ property (\(w :: Word64) -> packBits (unpackBits w) `shouldBe` w)
    -- it "encode decode law" $ property (\(bs :: [Bool]) -> 
    --   if length bs <=64 then unpackBits (packBits bs) `shouldBe` bs else pure ())
  describe "encodeTrans" $ do
    it "encodes a random trans" $
      encodeTrans 5 randomTrans `shouldBe`
        [True, True, False, False, True]
  describe "encode decode law" $ do
    it "random transition" $ 
      decodeTrans 3 (encodeTrans 3 randomTrans) `shouldBe` randomTrans
    it "words" $ do
      property (\(t@(Turing n _) :: Turing) -> decodeTM n (encodeTM t) `shouldBe` t)
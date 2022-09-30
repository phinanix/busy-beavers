module ParsingSpec where


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
import Text.Parsec
import Parsing

num = finiteCount
inum = finiteInfCount



spec :: Spec
spec = do
  describe "parseCount" $ do 
    it "parses a number" $ 
      runParser parseCount () "test" "3" `shouldBe` Right (num 3)
    it "parses some vars" $ 
      runParser (parseCount <* eof) () "test" "5+2*x_0+x_1" `shouldBe` 
        Right (num 5 <> boundVarCount (BoundVar 0) 2 <> boundVarCount (BoundVar 1) 1)
    it "doesn't parse malformed vars" $ 
      runParser (parseCount >> eof) () "test" "5+2x_0+x_1" `shouldSatisfy` has _Left 
  describe "parseCountSymbol" $ do 
    it "parses a pair" $ 
      runParser (parseCountSymbolPair (parseVecBit @2) <* eof) () "test" "(FF, 5+2*a_0+x_1)" 
        `shouldBe` Right (V.fromList [Bit False, Bit False], 
          num 5 <> boundVarCount (BoundVar 1) 1 <> symbolVarCount (SymbolVar 0) 2)
  describe "parseExpTape" $ do 
    it "parses a tape" $ 
      parse (parseExpTape (parseVecBit @2) <* eof) "test" "[(FF, 5+2*a_0+x_1)] >TT< [(TF, 3) (FT, x_2)]" 
        `shouldBe` Right (ExpTape 
          [(V.fromList [Bit False, Bit False], num 5 <> boundVarCount (BoundVar 1) 1 <> symbolVarCount (SymbolVar 0) 2)]
          (V.fromList [Bit True, Bit True])
          [(V.fromList [Bit True, Bit False], num 3), (V.fromList [Bit False, Bit True], boundVarCount (BoundVar 2) 1)])
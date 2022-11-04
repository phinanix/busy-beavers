module AggregateSpec where


import Relude
import Control.Lens

import Test.Hspec
import Test.QuickCheck
import Control.Exception (evaluate)

import Aggregate 
import Data.Char

spec :: Spec
spec = do
  describe "insertMaxKBy" $ do
    it "inserts less than k" $ let
      --0F -> TR1
      prev = [8, 5, 3]
      ans = [9, 8, 5, 3]
      in
      insertMaxKBy 5 (flip compare) 9 prev `shouldBe` ans 
    it "displaces at k" $ let 
      prev = [8, 5, 3]
      ans = [8, 6, 5] 
      in 
      insertMaxKBy 3 (flip compare) 6 prev `shouldBe` ans 
    it "doesn't displace if smaller" $ let 
      prev = [8, 5, 3]
      in 
      insertMaxKBy 3 (flip compare) 2 prev `shouldBe` prev
  describe "runStats" $ do 
    it "aggregates some characters" $ let 
      countLetters :: Statistic Char = Statistic isAlpha Count 
      smallestDigits = Statistic isDigit (MaxKBy 2 compare) 
      res :: [StatsResult Char] = [CountRes 35, MaxKByRes ['0', '0']]
      inStr :: String = "asdv98hasdfer890qweqw09qwe9vqy 0qw89ewq*W)(*R(*#)jfasdJ"
      in 
         snd <$> runStats [countLetters, smallestDigits] inStr `shouldBe` res 
  
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Parsing where

import Relude hiding (many)
import qualified Relude.Unsafe as U
import Control.Lens

import Data.Vector.Fixed (Arity)
import qualified Data.Vector.Fixed as V
import Data.Vector.Fixed.Unboxed
import Text.Parsec.Text
import Text.Parsec hiding ((<|>))
import qualified Data.Map.Monoidal as M

import Turing
import Util
import Count
import SimulateVecBit
import Data.Char (digitToInt)
import ExpTape

parseTrue :: GenParser st Bit
parseTrue = char 'T' >> pure (Bit True)

parseFalse :: GenParser st Bit
parseFalse = char 'F' >> pure (Bit False)

parseBit :: GenParser st Bit
parseBit = parseTrue <|> parseFalse

parseVecBit :: forall n st. (Arity n) => GenParser st (Vec n Bit)
parseVecBit = V.fromList' <$> count vecLen parseBit where
  vecLen = fromIntegral $ natVal (Proxy @n)

charToNat :: (Num n) => Char -> n
charToNat = fromIntegral . digitToInt

positiveNatural :: (Num a) => GenParser st a
positiveNatural = foldl' (\a i -> a * 10 + charToNat i) 0 <$> many1 digit

parseVar :: Char -> GenParser st (Int, Sum Natural)
parseVar c = times <|> noTimes where
  noTimes = (, 1) <$> parseInner
  times = do
    n <- positiveNatural
    char '*'
    s <- parseInner
    pure (s, n)
  parseInner = do
    char c
    char '_'
    positiveNatural

parseSymbolVar :: GenParser st (SymbolVar, Sum Natural)
parseSymbolVar = first SymbolVar <$> parseVar 'a'

parseBoundVar :: GenParser st (BoundVar, Sum Natural)
parseBoundVar = first BoundVar <$> parseVar 'x'

-- mySepBy :: GenParser st a -> GenParser st sep -> GenParser st [a]
-- mySepBy thing sep = do
--      stuff <- many (try (thing <* sep))
--      lastThing <- try thing
--      pure $ stuff ++ [lastThing]

parseCount :: GenParser st Count
parseCount = try fullCount <|> justNum where
  justNum = do
    c <- FinCount <$> positiveNatural
    notFollowedBy (char '*')
    pure c
  svOrBv = Left <$> try parseSymbolVar <|> Right <$> try parseBoundVar
  fullCount = do
    n <- option 0 $ try $ do
      x <- positiveNatural
      char '+'
      pure x
    vars <- sepBy svOrBv (char '+')
    if null vars then unexpected "no variables" else pure ()
    let (svs, bvs) = partitionEithers vars
    pure $ Count n (M.fromList svs) (M.fromList bvs)

parsePair :: GenParser st a -> GenParser st b -> GenParser st (a, b)
parsePair aParse bParse = do
  char '('
  a <- aParse
  char ','
  char ' '
  b <- bParse
  char ')'
  pure (a, b)

parseCountSymbolPair :: GenParser st s -> GenParser st (s, Count)
parseCountSymbolPair symParser = parsePair symParser parseCount

parseExpTape :: GenParser st s -> GenParser st (ExpTape s Count)
parseExpTape symParser = do
  char '['
  revLS <- sepBy (parseCountSymbolPair symParser) (char ' ')
  char ']'
  char ' '
  char '>'
  b <- symParser
  char '<'
  char ' '
  char '['
  rs <- sepBy (parseCountSymbolPair symParser) (char ' ')
  char ']'
  pure (ExpTape (reverse revLS) b rs)

parsePhase :: GenParser st Phase
parsePhase = do
  string "Phase "
  Phase <$> positiveNatural

parsePhaseET :: GenParser st s -> GenParser st (Phase, ExpTape s Count)
parsePhaseET symParser = parsePair parsePhase $ parseExpTape symParser

-- 1RB0RB_1LC1RA_0LA1LD_0LE0LC_1RA---

parseBBCBit :: GenParser st Bit
parseBBCBit = parseT <|> parseF where
  parseT = char '1' $> Bit True
  parseF = char '0' $> Bit False

parseDir :: GenParser st Dir
parseDir = parseL <|> parseR where
  parseL = char 'L' $> L
  parseR = char 'R' $> R

parseBBCPhase :: GenParser st Phase
parseBBCPhase = do
  letter <- upper
  pure $ Phase $ ord letter - ord 'A'

-- Nothing means --- means undefined 
--warning: when parsing a halt transition, we discard what you say to do and instead 
--just do the default thing: left and write true
parseBBTrans :: GenParser st (Maybe Trans)
parseBBTrans = parseDef <|> parseUndef where
  parseUndef = string "---" $> Nothing
  parseDef :: GenParser st (Maybe Trans)
  parseDef = Just <$> do
    b <- parseBBCBit
    d <- parseDir
    p <- parseBBCPhase
    pure $ if p == Phase 25 then Halt else Step p b d


parseBBChallenge :: Int -> GenParser st Turing
parseBBChallenge n = Turing n . fromList . concat <$> traverse parsePair (Phase <$> [0.. n-1]) 
  where 
  parsePair ph = do 
    t1 <- parseBBTrans
    t2 <- parseBBTrans
    if ph == Phase (n - 1) then pure '_' else char '_'
    pure $ mapMaybe (\case 
     (_e, Nothing) -> Nothing 
     (e, Just t) -> Just (e, t) ) [((ph, Bit False), t1), ((ph, Bit True), t2)]
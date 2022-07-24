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

parseMap :: (a -> b) -> GenParser st a -> GenParser st b
parseMap = fmap

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
positiveNatural =
    foldl' (\a i -> a * 10 + charToNat i) 0 <$> many1 digit

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

mySepBy :: GenParser st a -> GenParser st sep -> GenParser st [a]
mySepBy thing sep = do
     stuff <- many (try (thing <* sep))
     lastThing <- try thing
     pure $ stuff ++ [lastThing]

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


parseCountSymbolPair :: GenParser st s -> GenParser st (s, Count)
parseCountSymbolPair symParser = do
    char '('
    s <- symParser
    char ','
    char ' '
    c <- parseCount
    char ')'
    pure (s, c)

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
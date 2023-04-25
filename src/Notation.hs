module Notation where

import Relude
import qualified Relude.Unsafe as U
import Control.Lens
import Data.Char
import qualified Data.Text as T
import Prettyprinter
import qualified Data.Map.Monoidal as M

import Turing
import Util
import Count
--import Skip
import ExpTape



{-
The goal of this file is to define functions which convert between in memory 
Turing machines and a compact, easy to parse string representation. Each 
transition is represented like TR3, a three character string. 
1. T or F, representing the bit which is written.
2. L or R, representing the direction the head goes.
3. a number, representing the new state which is transitioned to, or H for halt. 
   (0-9 is all that is currently supported)
These transitions are packed together into a string like so:
FL1FR0TL2TLHTR0TL2
Each group of three characters corresponds to one transition; the transitions are ordered
starting with (state 1, reading false), (state 1, reading true), (state 2, reading false),
and so on. 
Three underscores are used if a machine does not have a particular transition defined.  
A machine is assumed to start in state 0.

There is a "canonical form" for a TM, which has TLH as the halting transition, 
In "tree form", it has TR2 (or FR2 depending on context) as the first transition and states 
are numbered in the order they are used. In "lex form", states are numbered in the order they 
appear in the string (1 is an exception)
-}

transToNotation :: Maybe Trans -> Text
transToNotation = \case
    Nothing -> "___"
    Just Halt -> "TLH"
    Just (Step ph b dir) -> dispBit b <> show dir <> show (unPhase ph)

transToBBNotation :: Maybe Trans -> Text
transToBBNotation = \case
    Nothing -> "---"
    Just Halt -> "1RH"
    Just (Step ph (Bit b) dir) -> let 
     bit = if b then '1' else '0'
     ab = "ABCDEFG"
     phaseLetter = ab U.!! unPhase ph
     in 
     fromString $ [bit] <> show dir <> [phaseLetter]
    --dispBit b <> show dir <> show (unPhase ph)

edgesOfLen :: Int -> [Edge]
edgesOfLen n = bind (\x -> (x,) <$> [Bit False, Bit True]) (Phase <$> [0.. n-1])

machineToNotation :: Turing -> Text
machineToNotation (Turing n trans) = T.concat $ transToNotation <$> transes where
    transes = (\e -> trans ^. at e) <$> edgesOfLen n

machineToBBNotation :: Turing -> Text
machineToBBNotation (Turing n trans) = T.intercalate "_" $ concatPairs $ transToBBNotation <$> transes where
    transes = (\e -> trans ^. at e) <$> edgesOfLen n
    go next = \case 
      (Nothing, xs) -> (Just next, xs)
      (Just prev, xs) -> (Nothing, (next<>prev):xs)
    package = \case 
      (Nothing, xs) -> xs 
      (Just _, xs) -> error "paired up an odd length list"
    concatPairs :: [Text] -> [Text]
    concatPairs = package . foldl' (flip go) (Nothing, [])

parseBit' :: Char -> Either Text Bit
parseBit' = \case
  'T' -> Right $ Bit True
  'F' -> Right $ Bit False
  other -> Left $ "got " <> show other <> " for bit"

parseDir :: Char -> Either Text Dir
parseDir = \case
  'L' -> Right L
  'R' -> Right R
  other -> Left $ "got " <> show other <> " for dir"

parsePhase :: Char -> Either Text Phase
parsePhase stateChar = do
    guardMsg (isDigit stateChar) ("stateChar was not digit: " <> show stateChar)
    pure $ Phase $ digitToInt stateChar

--the maybe being nothing means the machine does not have this trans defined
notationToTrans :: Char -> Char -> Char -> Either Text (Maybe Trans)
notationToTrans '_' '_' '_' = Right Nothing
notationToTrans bitChar dirChar stateChar = case stateChar of
  'H' -> Right (Just Halt)
  stateDigit -> do
      bit <- parseBit' bitChar
      dir <- parseDir dirChar
      ph <- parsePhase stateDigit
      pure $ Just $ Step ph bit dir

parseTrans :: Text -> Either Text (Maybe Trans)
parseTrans inp = case T.unpack inp of
    [bitChar, dirChar, stateChar] -> notationToTrans bitChar dirChar stateChar
    other -> error $ "tried to parseTrans: " <> T.pack other

notationToMachine :: Text -> Either Text Turing
notationToMachine inp =
  let chunks = T.chunksOf 3 inp in
  --empty string is not a machine, machines need an even number of transitions since they have
  --two per phase
  case chunks of
    [] -> Left "got empty string"
    (x : xs) -> do
      let neChunks = x :| xs
      guardMsg (even (length neChunks))
        ("neChunks not even len length: " <> show (length neChunks)
          <> " and list: "  <> show neChunks)
      let numPh = length neChunks `div` 2
      guardMsg (T.length (last neChunks) == 3)
        ("string length not a multiple of 3: " <> show neChunks)
      transes <- toList <$> traverse parseTrans neChunks
      let map = fromList $ catMaybes $ sequenceA <$> zip (edgesOfLen numPh) transes
      pure $ Turing numPh map

nm :: Text -> Either Text Turing
nm = notationToMachine

unsafeNotationToMachine :: Text -> Turing
unsafeNotationToMachine = unsafeFromRight . notationToMachine

unm :: Text -> Turing
unm = unsafeNotationToMachine

dispTuring :: Turing -> Text
dispTuring m@(Turing _ transitions) = ifoldMap dispET transitions <> machineToNotation m <> "\n"

instance Pretty Turing where
  pretty = pretty . dispTuring

{-
Notation for Config
[phase notation] [list of (bit notation, count notation)]>bit notation<[list of (bit notation, count notation)]
the first list is "backwards" ie it reads the normal way rather than the fucked way

Bit notation: T or F 
Phase notation: p(number)
Count notation: up to 1 number + one of each boundvar or symbolvar, separated by + signs
  Number notation: number
  Boundvar notation: n*x_i
  Symbolvar notation: m*a_j

Notation for skipend
either 
  [config]
or 
  < [list of (bit notation, count notation)]
or 
  [list of (bit notation, count notation)] >
-}

notationCount :: Count -> Text
notationCount (FinCount n) = show n
notationCount (Count n as xs) = T.concat $ intersperse "+" symbolList where
  symbolList = (if n > 0 then (show n :) else id)
    (nSymbolVar <$> M.assocs as) ++ (nBoundVar <$> M.assocs xs)
  nBoundVar (BoundVar i, Sum n) = if n == 1 
    then "x_" <> show i 
    else show n <> "*x_" <> show i
  nSymbolVar (SymbolVar i, Sum n) =  if n == 1 
    then "a_" <> show i 
    else show n <> "*a_" <> show i

notationBitCount :: (Bit, Count) -> Text
notationBitCount (b, c) = "(" <> dispBit b <> ", " <> notationCount c <> ") "

notationPhase :: Phase -> Text
notationPhase (Phase i) = "p" <> show i <> " "

notationTape :: ExpTape Bit Count -> Text
notationTape (ExpTape ls p rs)
  =  dispBitCountList (reverse ls)
  <> " >" <> dispBit p <> "< " 
  <> dispBitCountList rs
  where 
    dispBitCountList [] = "[]"
    dispBitCountList xs = "[" <> T.init (T.concat (notationBitCount <$> xs)) <> "]"

{- notationSkipEnd :: TapePush Count Bit -> Text 
notationSkipEnd = \case 
  Middle tape -> notationTape tape 
  Side L xs -> "< " <> T.concat (notationBitCount <$> xs) 
  Side R xs -> T.concat (notationBitCount <$> reverse xs) <> " >"
 -}
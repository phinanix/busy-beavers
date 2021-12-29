module Notation where

import Relude
import qualified Relude.Unsafe as U
import Control.Lens
import Data.Char 
import qualified Data.Text as T
import Prettyprinter

import Turing
import Util
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

edgesOfLen :: Int -> [Edge] 
edgesOfLen n = bind (\x -> (x,) <$> [False, True]) (Phase <$> [0.. n-1])

machineToNotation :: Turing -> Text
machineToNotation (Turing n trans) = T.concat $ transToNotation <$> transes where
    transes = (\e -> trans ^. at e) <$> edgesOfLen n

parseBit :: Char -> Either Text Bit
parseBit = \case 
  'T' -> Right True 
  'F' -> Right False 
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
      bit <- parseBit bitChar 
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
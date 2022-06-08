module Tape where

import Relude
import Relude.Unsafe as Unsafe (init, last)
import Control.Lens
import Prettyprinter 

import Turing
import Util

data Tape s = Tape
  { left :: [s]
  , point :: s
  , right :: [s]
  } deriving (Eq, Ord, Show, Generic)
instance NFData s => NFData (Tape s)


--this function should not accumulates zeros where they are redundant
--functions to move the point of the tape left and right
--returning nothing if the list ends
tapeLeft :: Tape Bit -> Tape Bit
--when we'd stack an false bit onto the implicitly infinite stack of False,
--drop it instead
tapeLeft (Tape [] (Bit False) []) = Tape [] (Bit False) []
tapeLeft (Tape (l : ls) (Bit False) []) = Tape ls l []
tapeLeft (Tape [] h rs) = Tape [] (Bit False) (h : rs)
tapeLeft (Tape (l : ls) h rs) = Tape ls l (h : rs)

tapeRight :: Tape Bit -> Tape Bit
--analagous to above
tapeRight (Tape [] (Bit False) []) = Tape [] (Bit False) []
tapeRight (Tape [] (Bit False) (r : rs)) = Tape [] r rs
tapeRight (Tape ls h []) = Tape (h : ls) (Bit False) []
tapeRight (Tape ls h (r : rs)) = Tape (h : ls) r rs

mirrorTape :: Tape Bit -> Tape Bit
mirrorTape (Tape ls h rs) =  Tape rs h ls

dispTape :: Tape Bit -> Text
dispTape (Tape ls h rs) = dispBits (reverse ls) <> ">" <> dispBit h <> "<" <> dispBits rs where
  dispBits :: [Bit] -> Text
  dispBits [] = ""
  dispBits bits = mconcat ((\i -> dispBit i <> " ") <$> Unsafe.init bits)
    <> dispBit (Unsafe.last bits)

instance Pretty (Tape Bit) where 
  pretty = prettyText . dispTape 

--a class for things like tapes where you can count the ones
class Tapeable tape where
  ones :: tape -> Int

instance Tapeable (Tape Bit) where
  ones (Tape ls h rs) = length $ filter (== Bit True) $ ls <> rs <> [h]

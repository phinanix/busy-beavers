module ExpTape where

import Relude
import Control.Lens

import Turing

data ExpTape s c = ExpTape
  { left :: [(s, c)]
  , point :: (s, c, Dir) --whether the machine is on the L or the R of the block of bits
  , right :: [(s, c)]
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s, NFData c) => NFData (ExpTape s c)

--split modify into modifyPointUnderHead and moveTapeADirection
modify :: Dir -> Bit -> ExpTape Bit Int -> ExpTape Bit Int
modify L newBit (ExpTape [] (bit, num, L) rs) = ExpTape [] (False, 1, R) $ rest newBit bit num rs
modify L newBit (ExpTape ((lbit, lnum):ls) (bit, num, L) rs) = ExpTape ls (lbit, lnum, R) $ rest newBit bit num rs
modify L newBit (ExpTape ls (bit, num, R) rs) = let newRs = (newBit, 1) : rs in
  if num == 1
  then case ls of
    [] -> ExpTape [] (False, 1, R) newRs
    (lbit, lnum):ls -> ExpTape ls (lbit, lnum, R) newRs
  else ExpTape ls (bit, num-1, R) newRs


rest :: Bit -> Bit -> Int -> [(Bit, Int)] -> [(Bit, Int)]
rest newBit bit num list = if newBit == bit then (bit, num) : list else
  if num-1 == 0 then (newBit, 1) : list else
  (newBit, 1) : (bit, (num-1)) : list

tapeLeft :: ExpTape Bit Int -> ExpTape Bit Int
tapeLeft (ExpTape [] (False, _, _) []) = ExpTape [] (False, 1, R) []
tapeLeft (ExpTape [] (bit, num, _) rs) = ExpTape [] (False, 1, R) $ (bit, num):rs
tapeLeft (ExpTape ((lbit, lnum):ls) (False, _, _) []) = ExpTape ls (lbit, lnum, R) []
tapeLeft (ExpTape ((lbit, lnum):ls) (bit, num, _) rs) = ExpTape ls (lbit, lnum, R) $ (bit, num):rs


tapeRight :: ExpTape Bit Int -> ExpTape Bit Int
tapeRight (ExpTape [] (False, _, _) []) = ExpTape [] (False, 1, R) []
tapeRight (ExpTape ls (bit, num, _) []) = ExpTape ((bit, num):ls) (False, 1, R) []
tapeRight (ExpTape [] (False, _, _) ((rbit, rnum):rs)) = ExpTape [] (rbit, rnum, L) rs
tapeRight (ExpTape ls (bit, num, _) ((rbit, rnum):rs)) = ExpTape ((bit,num):ls) (rbit, rnum, L) rs

tapeMove :: Dir -> ExpTape Bit Int -> ExpTape Bit Int
tapeMove L = tapeLeft
tapeMove R = tapeRight

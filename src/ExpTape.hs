module ExpTape where

import Relude
import Control.Lens

import Turing
import Skip

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

--TODO:: this function tells us we should probably be using Seq instead of list
--appends two lists, keeping the ExpTape invariant that there are never contiguous
--blocks of the same symbol
etApp :: (Eq s, Semigroup c) => [(s, c)] -> [(s, c)] -> [(s, c)]
etApp [] ys = ys
etApp xs [] = xs
etApp (fromList -> xs) (y : ys) = if fst (last xs) == fst y
  then init xs <> [(fst y, snd (last xs) <> snd y)] <> ys
  else toList $ xs <> (y :| ys)

glomPointLeft :: (Eq s, Semigroup c) => ExpTape s c -> ExpTape s c
glomPointLeft (ExpTape ((s_l, c_l):ls) (s_p, c_p, dir) rs) | s_l == s_p =
  ExpTape ls (s_p, c_p <> c_l, dir) rs
glomPointLeft e = e

glomPointRight :: (Eq s, Semigroup c) => ExpTape s c -> ExpTape s c
glomPointRight (ExpTape ls (s_p, c_p, dir) ((s_r, c_r):rs)) | s_p == s_r =
  ExpTape ls (s_p, c_p <> c_r, dir) rs
glomPointRight e = e

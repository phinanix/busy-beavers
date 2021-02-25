module ExpTape where

import Relude
import Control.Lens

import Turing
import Count
import Tape

--when the machine is pointing to a block containing one symbol, then it isn't on a particular side
--else it's pointing to a count, which is not 1, and it's on one side of that count
data Location c = One | Side c Dir deriving (Eq, Ord, Show, Generic)
instance (NFData c) => NFData (Location c)

$(makePrisms ''Location)


data ExpTape s c = ExpTape
  { left :: [(s, c)]
  , point :: (s, Location c)
  , right :: [(s, c)]
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s, NFData c) => NFData (ExpTape s c)

--TODO:: split modify into modifyPointUnderHead and moveTapeADirection
--or otherwise refactor it - it's a mess
-- modify :: Dir -> Bit -> ExpTape Bit Int -> ExpTape Bit Int
-- modify = undefined
-- modify L newBit (ExpTape [] (bit, num, L) rs) = ExpTape [] (False, 1, R) $ rest newBit bit num rs
-- modify L newBit (ExpTape ((lbit, lnum):ls) (bit, num, L) rs) = ExpTape ls (lbit, lnum, R) $ rest newBit bit num rs
-- modify L newBit (ExpTape ls (bit, num, R) rs) = let newRs = (newBit, 1) : rs in
--   if num == 1
--   then case ls of
--     [] -> ExpTape [] (False, 1, R) newRs
--     (lbit, lnum):ls -> ExpTape ls (lbit, lnum, R) newRs
--   else ExpTape ls (bit, num-1, R) newRs


-- rest :: Bit -> Bit -> Int -> [(Bit, Int)] -> [(Bit, Int)]
-- rest newBit bit num list = if newBit == bit then (bit, num) : list else
--   if num-1 == 0 then (newBit, 1) : list else
--   (newBit, 1) : (bit, (num-1)) : list
--
-- tapeLeft :: ExpTape Bit Int -> ExpTape Bit Int
-- tapeLeft (ExpTape [] (False, _, _) []) = ExpTape [] (False, 1, R) []
-- tapeLeft (ExpTape [] (bit, num, _) rs) = ExpTape [] (False, 1, R) $ (bit, num):rs
-- tapeLeft (ExpTape ((lbit, lnum):ls) (False, _, _) []) = ExpTape ls (lbit, lnum, R) []
-- tapeLeft (ExpTape ((lbit, lnum):ls) (bit, num, _) rs) = ExpTape ls (lbit, lnum, R) $ (bit, num):rs
--
--
-- tapeRight :: ExpTape Bit Int -> ExpTape Bit Int
-- tapeRight (ExpTape [] (False, _, _) []) = ExpTape [] (False, 1, R) []
-- tapeRight (ExpTape ls (bit, num, _) []) = ExpTape ((bit, num):ls) (False, 1, R) []
-- tapeRight (ExpTape [] (False, _, _) ((rbit, rnum):rs)) = ExpTape [] (rbit, rnum, L) rs
-- tapeRight (ExpTape ls (bit, num, _) ((rbit, rnum):rs)) = ExpTape ((bit,num):ls) (rbit, rnum, L) rs
--
-- tapeMove :: Dir -> ExpTape Bit Int -> ExpTape Bit Int
-- tapeMove L = tapeLeft
-- tapeMove R = tapeRight

--TODO:: this function tells us we should probably be using Seq instead of list
--appends two lists, keeping the ExpTape invariant that there are never contiguous
--blocks of the same symbol
etApp :: (Eq s, Semigroup c) => [(s, c)] -> [(s, c)] -> [(s, c)]
etApp [] ys = ys
etApp xs [] = xs
etApp (fromList -> xs) (y : ys) = if fst (last xs) == fst y
  then init xs <> [(fst y, snd (last xs) <> snd y)] <> ys
  else toList $ xs <> (y :| ys)

invariantifyList :: (Eq s, Semigroup c) => [(s, c)] -> [(s, c)]
invariantifyList ((s, c) : (t, d) : xs) | s == t = invariantifyList ((s, c <> d):xs)
invariantifyList (x : xs) = x : invariantifyList xs
invariantifyList [] =  []

glomPointLeft :: (Eq s) => ExpTape s InfCount -> ExpTape s InfCount
glomPointLeft (ExpTape ((s_l, c_l):ls) (s_p, One) rs) | s_l == s_p =
  ExpTape ls (s_p, Side (NotInfinity (finiteCount 1) <> c_l) R) rs
--note: suppose you're at the left of two ones and to your
--left is two more ones. you can't glom at all, that's why the Side has to be R
glomPointLeft (ExpTape ((s_l, c_l):ls) (s_p, Side c_p R) rs) | s_l == s_p =
  ExpTape ls (s_p, Side (c_p <> c_l) R) rs
glomPointLeft e = e

glomPointRight :: (Eq s) => ExpTape s InfCount -> ExpTape s InfCount
glomPointRight (ExpTape ls (s_p, One) ((s_r, c_r):rs)) | s_p == s_r =
  ExpTape ls (s_p, Side (NotInfinity (finiteCount 1) <> c_r) L) rs
glomPointRight (ExpTape ls (s_p, Side c_p L) ((s_r, c_r):rs)) | s_p == s_r =
  ExpTape ls (s_p, Side (c_p <> c_r) L) rs
glomPointRight e = e

glomPoint :: (Eq s) => ExpTape s InfCount -> ExpTape s InfCount
glomPoint = glomPointLeft . glomPointRight

dispBitCount :: (Bit, InfCount) -> Text
dispBitCount (b, c) = "(" <> dispBit b <> ", " <> dispInfCount c <> ") "

dispPoint :: (Bit, Location InfCount) -> Text
dispPoint (bit, Side count L) = "|>" <> dispBitCount (bit, count)
dispPoint (bit, Side count R) = dispBitCount (bit, count) <> "<|"
dispPoint (bit, One) = dispBitCount (bit, NotInfinity $ finiteCount 1) <> "<|"

dispExpTape :: ExpTape Bit InfCount -> Text
dispExpTape (ExpTape ls point rs)
  = (mconcat $ dispBitCount <$> reverse ls)
  <> dispPoint point
  <> (mconcat $ dispBitCount <$> rs)

instance Tapeable (ExpTape Bit InfCount ) where
  ones (ExpTape ls point rs) = countPoint point + countList ls + countList rs where
    countPoint (False, _) = 0
    countPoint (True, One) = 1
    countPoint (True, Side c _) = infCountToInt c
    countList :: [(Bit, InfCount)] -> Int
    countList = getSum . foldMap Sum . mapMaybe (\(bit, c) -> guard bit $> infCountToInt c)

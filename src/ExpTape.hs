module ExpTape where

import Relude
import qualified Relude.Unsafe as Unsafe (init)
import Control.Lens
import Prettyprinter 

import Turing
import Count
import Tape
import Data.Bitraversable (Bitraversable)
import Relude (Bifoldable)


data ExpTape s c = ExpTape
  { left :: [(s, c)]
  , point :: s
  , right :: [(s, c)]
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s, NFData c) => NFData (ExpTape s c)

instance Bifunctor ExpTape where 
  first :: (a -> b) -> ExpTape a c -> ExpTape b c 
  first f (ExpTape ls p rs) = ExpTape (first f <$> ls) (f p) (first f <$> rs)
  second :: (c -> d) -> ExpTape a c -> ExpTape a d 
  second g (ExpTape ls p rs) = ExpTape (second g <$> ls) p (second g <$> rs)

instance Bifoldable ExpTape where 
  bifoldMap = bifoldMapDefault 

instance Bitraversable ExpTape where
  bitraverse f g (ExpTape ls p rs) 
   = ExpTape <$> traverse (bitraverse f g) ls <*> f p <*> traverse (bitraverse f g) rs

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

-- glomPointLeft :: (Eq s, Countable c) => ExpTape s c -> ExpTape s c
-- glomPointLeft (ExpTape ((s_l, c_l):ls) (s_p, One) rs) | s_l == s_p =
--   ExpTape ls (s_p, Side (unit <> c_l) R) rs
-- --note: suppose you're at the left of two ones and to your
-- --left is two more ones. you can't glom at all, that's why the Side has to be R
-- glomPointLeft (ExpTape ((s_l, c_l):ls) (s_p, Side c_p R) rs) | s_l == s_p =
--   ExpTape ls (s_p, Side (c_p <> c_l) R) rs
-- glomPointLeft e = e

-- glomPointRight :: (Eq s, Countable c) => ExpTape s c -> ExpTape s c
-- glomPointRight (ExpTape ls (s_p, One) ((s_r, c_r):rs)) | s_p == s_r =
--   ExpTape ls (s_p, Side (unit <> c_r) L) rs
-- glomPointRight (ExpTape ls (s_p, Side c_p L) ((s_r, c_r):rs)) | s_p == s_r =
--   ExpTape ls (s_p, Side (c_p <> c_r) L) rs
-- glomPointRight e = e

-- glomPoint :: (Eq s, Countable c) => ExpTape s c -> ExpTape s c
-- glomPoint = glomPointLeft . glomPointRight

dispBitCount :: (Pretty s) => (s, Count) -> Text
dispBitCount (b, c) = "(" <> show (pretty b) <> ", " <> dispCount c <> ") "

dispBitICount :: (Bit, InfCount) -> Text
dispBitICount (b, c) = "(" <> dispBit b <> ", " <> dispInfCount c <> ") "

dispPoint :: (Pretty s) => s -> Text
dispPoint bit = "|>" <> show (pretty bit) <> "<|"

dispExpTape :: ExpTape Bit InfCount -> Text
dispExpTape (ExpTape ls point rs)
  = mconcat (dispBitICount <$> reverse ls)
  <> dispPoint point
  <> mconcat (dispBitICount <$> rs)

instance Tapeable (ExpTape Bit InfCount) where
  ones (ExpTape ls point rs) = countPoint point + countList ls + countList rs where
    countPoint b = if b then 1 else 0
    countList :: [(Bit, InfCount)] -> Int
    countList = getSum . foldMap Sum . mapMaybe (\(bit, c) -> guard bit $> infCountToInt c)

getNewPoint :: [(s, InfCount)] -> Maybe (s, [(s, InfCount)])
getNewPoint [] = Nothing
getNewPoint xs@((b, Infinity) : _) = Just (b, xs)
getNewPoint  ((b, NotInfinity c) : xs) = if c == finiteCount 1
  then Just (b, xs)
  else Just (b, (b, NotInfinity $ unsafeSubNatFromCount c 1) : xs)

expTapeToTape :: ExpTape Bit InfCount -> Tape
expTapeToTape (ExpTape left point right) = Tape newLeft point newRight where
  intify :: [(s, InfCount)] -> [(s, Int)]
  intify = fmap $ fmap infCountToInt
  flatten :: [(s, Int)] -> [s]
  flatten = foldMap $ uncurry (flip replicate)
  newLeft = flatten $ intify $ Unsafe.init left
  newRight = flatten $ intify $ Unsafe.init right
module ExpTape where

import Relude
import qualified Relude.Unsafe as Unsafe (init)
import Control.Lens
import Prettyprinter
import Data.Bitraversable (Bitraversable)
import Control.Exception (assert)
import Relude.Extra (bimapBoth)
import Safe.Partial

import Turing
import Count
import Tape
import Util
import Data.Aeson

data ExpTape s c = ExpTape
  { left :: [(s, c)]
  , point :: s
  , right :: [(s, c)]
  } deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s, NFData c) => NFData (ExpTape s c)
instance (ToJSON s, ToJSON c) => ToJSON (ExpTape s c) where 
    toEncoding = genericToEncoding defaultOptions

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

listSatisfiesInvariant :: (Eq s, Monoid c, Ord c) => [(s, c)] -> Bool 
listSatisfiesInvariant inp = allPositive && allDiff where 
  allPositive = all (> mempty) (snd <$> inp)
  allDiff = case inp of 
    [] -> True
    x : xs -> let 
      neInp = x :| xs 
      pairs = zip (init neInp) (tail neInp)
      in 
        not $ any (uncurry (==)) pairs

etSatisfiesInvariant :: (Eq s, Monoid c, Ord c) => ExpTape s c -> Bool 
etSatisfiesInvariant (ExpTape ls p rs) = listSatisfiesInvariant ls && listSatisfiesInvariant rs
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
dispBitCount (b, c) = "(" <> showP b <> ", " <> showP c <> ") "

-- dispBitICount :: (Bit, InfCount) -> Text
-- dispBitICount (b, c) = "(" <> dispBit b <> ", " <> dispInfCount c <> ") "

dispETPair :: (Pretty b, Pretty c) => (b, c) -> Text
dispETPair (b, c) = "(" <> showP b <> ", " <> showP c <> ") "

dispPoint :: (Pretty s) => s -> Text
dispPoint bit = "|>" <> show (pretty bit) <> "<|"

dispExpTape :: (Pretty b, Pretty c) => ExpTape b c -> Text
dispExpTape (ExpTape ls point rs)
  = mconcat (dispETPair <$> reverse ls)
  <> dispPoint point
  <> mconcat (dispETPair <$> rs) 
  <> "\n"

instance (Pretty b, Pretty c) => Pretty (ExpTape b c) where 
  pretty = pretty . dispExpTape 
  
countPoint :: Num p => Bool -> p
countPoint b = if b then 1 else 0
countList :: [(Bit, InfCount)] -> Int
countList = getSum . foldMap Sum . mapMaybe (\(Bit bit, c) -> guard bit $> infCountToInt c)

instance Tapeable (ExpTape Bit InfCount) where
  ones (ExpTape ls (Bit point) rs) = countPoint point + countList ls + countList rs where
    
getNewPoint :: [(s, InfCount)] -> Either Text (s, [(s, InfCount)])
getNewPoint [] = Left "tape Empty"
getNewPoint xs@((b, Infinity) : _) = pure (b, xs)
getNewPoint  ((b, NotInfinity c) : xs) = if c == finiteCount 1
  then pure (b, xs)
  else case subNatFromCount c 1 of
    Nothing -> Left $ "count didn't have an extra" <> show c
    Just newC -> pure (b, (b, NotInfinity newC) : xs)

getNewFinPoint :: [(s, Count)] -> Maybe (s, [(s, Count)])
getNewFinPoint [] = Nothing
getNewFinPoint  ((b, c) : xs) = if c == finiteCount 1
  then Just (b, xs)
  else subNatFromCount c 1 <&> (\newC -> (b, (b, newC) : xs))

expTapeToTape :: ExpTape Bit InfCount -> Tape Bit
expTapeToTape (ExpTape left point right) = Tape (tapeHalfToBitList left) point (tapeHalfToBitList right) where

tapeHalfToBitList :: Partial => [(s, InfCount)] -> [s]
tapeHalfToBitList = flatten . intify . Unsafe.init  where 
  intify :: [(s, InfCount)] -> [(s, Int)]
  intify = fmap $ fmap infCountToInt
  flatten :: [(s, Int)] -> [s]
  flatten = foldMap $ uncurry (flip replicate)

data Signature s = Signature [s] s [s] deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (Signature s)

dispSignature :: Pretty s => Signature s -> Text
dispSignature (Signature ls p rs) = mconcat (showP <$> reverse ls) 
  <> dispPoint p 
  <> mconcat (showP <$> rs)

instance Pretty s => Pretty (Signature s) where 
  pretty = prettyText . dispSignature 

tapeSignature :: ExpTape s c -> Signature s
tapeSignature (ExpTape ls p rs) = Signature (fst <$> ls) p  (fst <$> rs)

--returns true if the first signature is a subsig of the second,
--ie if the tape matches the second, it will also match the first
isSubSignatureOf :: (Eq s) => Signature s -> Signature s -> Bool 
isSubSignatureOf (Signature ls p rs) (Signature ms q ss) 
  = (ls `isPrefixOf` ms) && (p == q) && (rs `isPrefixOf` ss)

getCounts :: ExpTape s c -> ([c], [c])
getCounts (ExpTape ls _p rs) = bimapBoth (fmap snd) (ls, rs)

signatureComplexity :: Signature s -> Int
signatureComplexity (Signature ls _p rs) = length ls + length rs

getNThings :: Partial => [(s, InfCount)] -> Natural -> [s]
getNThings _ 0 = [] 
getNThings xs n = case getNewPoint xs of 
  Left msg -> error $ "getNThings failed: " <> msg 
  Right (s, rest) -> (s :) $ getNThings rest (n - 1)

runLengthEncode :: (Eq s) => [s] -> [(s, Count)]
runLengthEncode xs = invariantifyList $ (, One) <$> xs 

getNFromRLE :: (Eq s, Partial) => [(s, InfCount)] -> Natural -> [(s, Count)] 
getNFromRLE xs n = runLengthEncode $ getNThings xs n

--given an exptape and a <=0 integer representing distance to go left (0 being take 
--nothing beyond the point) and a >=0 integer representing distance to go right (similarly) 
--return the corresponding new ExpTape
sliceExpTape :: (Eq s, Partial) => ExpTape s InfCount -> Int -> Int -> ExpTape s Count 
sliceExpTape (ExpTape ls p rs) lDist rDist = assert (lDist <= 0 && rDist >= 0) $ 
  ExpTape ls' p rs' where 
    ls' = getNFromRLE ls (fromIntegral (-lDist))
    rs' = getNFromRLE rs (fromIntegral rDist)
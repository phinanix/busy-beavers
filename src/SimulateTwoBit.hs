module SimulateTwoBit where

import Relude hiding (mapMaybe, filter, (??))
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))
import Data.List (maximumBy, foldl1)
import qualified Data.List.NonEmpty as NE ((<|))
import Data.Map.Strict (assocs, keysSet, unions)
import Witherable
import Prettyprinter
import Control.Exception
import Safe.Partial

import Util
import Turing
import ExpTape
import Skip
import Count
import HaltProof
import Results
import Glue
import Simulate (initSimState)

import SimulateSkip
{-
because we're on the left of the twobit, we can split transitions into two groups:
1) the transitions where we step left right away, where we need to make a skip for every
   pair of cur symbol and symbol to left
2) the transitions where we step right first, where we only need to make a skip for every
   cur symbol
-}
allInitTapes :: Turing -> [(Phase, ExpTape Bit Natural)]
allInitTapes (Turing _n trans) = concatMap toList
  $ (leftTransTapes <$> assocs leftTrans) ++ (rightTransTapes <$> assocs rightTrans)
  where
  transGoesLeft = \case
    Halt -> True
    (Step _ _ L) -> True
    (Step _ _ R) -> False
  splitBy p xs = (filter p xs, filter (not . p) xs)
  (leftTrans, rightTrans) = splitBy transGoesLeft trans

  allLeftTapes = (,1) <$$> ((:) <$> uniBit <*> (pure <$> uniBit))
  leftTransTapes ((p, b), _) = (p,) <$>
    ((\x y -> ExpTape x b [(y, 1)]) <$> allLeftTapes <*> uniBit)
  rightTransTapes ((p, b), _) = (p,) <$> ((\x -> ExpTape [] b [(x, 1)]) <$> uniBit)

data FlatTape s = FlatTape
  { left :: [s]
  , point :: s
  , right :: [s]
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (FlatTape s)

unRLE :: [(s, Natural)] -> [s]
unRLE = bind (\(s, n) -> genericReplicate n s)

rle :: forall s. (Eq s) => [s] -> [(s, Natural)]
rle = \case
  [] -> []
  x : xs -> let (f, rest) = pop (x :| xs) in
    f : rle rest
  where
  pop :: NonEmpty s -> ((s, Natural), [s])
  pop (x :| xs) = first (\ys -> (x, fromIntegral $ 1 + length ys)) $ break (/= x) xs

-- flattenET :: ExpTape s Natural -> FlatTape s
-- flattenET (ExpTape ls p rs) = FlatTape (unRLE ls) p (unRLE rs)

-- unFlattenET :: (Eq s) => FlatTape s -> ExpTape s Natural 
-- unFlattenET (FlatTape ls p rs) = ExpTape (rle ls) p (rle rs)

pairBitList :: [Bit] -> [TwoBit] 
pairBitList xs = uncurry TwoBit <$> pairs xs where 
  pairs :: [b] -> [(b, b)] 
  pairs = \case 
    [] -> []
    [_] -> error "given odd length list"
    (x : y : rest) -> (x, y) : pairs rest

unPairBitList :: [TwoBit] -> [Bit] 
unPairBitList = bind (\(TwoBit x y) -> [x, y])

etBitToTwoBit :: ExpTape Bit Natural -> ExpTape TwoBit Natural
etBitToTwoBit (ExpTape lpairs p rpairs) = case unRLE rpairs of 
  [] -> error "rs can't be empty"
  (r : rs) -> ExpTape (neaten $ unRLE lpairs) (TwoBit p r) (neaten rs) 
  where 
  neaten = rle . pairBitList 

etTwoBitToBit :: ExpTape TwoBit Natural -> ExpTape Bit Natural
etTwoBitToBit (ExpTape lpairs (TwoBit p r) rpairs) = let 
  ls = unPairBitList $ unRLE lpairs 
  rs = (r:) $ unPairBitList $ unRLE rpairs
  in 
  ExpTape (rle ls) p (rle rs) 


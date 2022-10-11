{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies          #-}
module SimulateVecBit where

import Relude hiding (mapMaybe, filter, (??))
import Control.Lens
import GHC.TypeNats
import Data.Map.Monoidal (MonoidalMap(..))
import Data.List (maximumBy, foldl1)
import qualified Data.List.NonEmpty as NE ((<|))
import Data.Map.Strict (keys, keysSet, unions)
import Witherable
import Prettyprinter
import Control.Exception ( assert )
import Safe.Partial
import Safe.Exact
import Control.Monad

import Data.Vector.Fixed hiding (toList, fromList, foldMap, Empty, length)
import qualified Data.Vector.Fixed as V
import Data.Vector.Fixed.Unboxed
import qualified Data.Vector.Fixed.Primitive as P

import Util
import Turing
import ExpTape
import Skip
import Count
import Simulate (TMState(..), PartialStepResult(..))
import TapeSymbol
import Tape
import HaltProof (HaltProof(Cycle))
import Data.Complex
import SimulateTwoBit
import Data.Vector.Fixed.Mutable (IVector (..), MVector (..))



ex :: Vec2 Bool
ex = mk2 False True

ex2 :: Vec 3 Bool
ex2 = mk3 False False True

com :: Complex Float
com = 0 :+ 0

dimComplex :: Dim Complex :~: 2
dimComplex = Refl


allBitsLengthN :: Natural -> NonEmpty [Bit]
allBitsLengthN n = if n == 0
    then [] :| []
    else bind (\xs -> (<| xs) <$> uniBit) $ allBitsLengthN (n - 1)

uniNBitList :: (KnownNat n) => p n -> NonEmpty [Bit]
uniNBitList p = allBitsLengthN $ natVal p

{-
The point of this function, is to give us all the tapes which are *made of Bits* that 
correspond to all the "basic" transitions (things like 2 >TT< -> 0 FT>|) so we can 
simulate them in Bit land. 
It could use a "universe" function and a "convert to bits" function, or it could use a 
"knownNat" type deal. 
-}
allInitTapes :: Natural -> Turing -> [(Phase, Tape Bit)]
allInitTapes n (Turing _n trans) = assert (n > 0) concatMap toList
  $ (leftTransTapes <$> keys leftTrans) ++ (rightTransTapes <$> keys rightTrans)
  where
  transGoesLeft :: Trans -> Bool
  transGoesLeft = \case
    Halt -> True
    (Step _ _ L) -> True
    (Step _ _ R) -> False
  splitBy :: (Filterable f) => (a -> Bool) -> f a -> (f a, f a)
  splitBy p xs = (filter p xs, filter (not . p) xs)
  (leftTrans, rightTrans) = splitBy transGoesLeft trans

  allLeftTapes = allBitsLengthN n
  allRightTapes = allBitsLengthN (n - 1)
  leftTransTapes (p, b) = (p,) <$>((\x y -> Tape x b y) <$> allLeftTapes <*> allRightTapes)
  rightTransTapes (p, b) = (p,) <$> (Tape [] b <$> allRightTapes)

listToVector :: forall v. (Vector v Bit, Partial) => [Bit] -> [v Bit]
listToVector l = case l of 
  [] -> []
  _ -> let
        vecLen = fromIntegral $ natVal (Proxy @(Dim v))
        (start, end) = splitAtExact vecLen l in
    (V.fromList' start :) $ listToVector end

tapeToVector :: forall v. (Vector v Bit) => Tape Bit -> Tape (v Bit)
tapeToVector (Tape ls p rs) = let
    dimV = natVal (Proxy @(Dim v))
    (pointList, restRs) = splitAtExact (fromIntegral dimV - 1) rs
    point = V.fromList' (p : pointList)
    in Tape (listToVector ls) point (listToVector restRs)


makeVectorSkip :: forall v. (Vector v Bit, Eq (v Bit))
    => Turing -> (Phase, Tape Bit) -> Skip Natural (v Bit)
makeVectorSkip t (startPh, startT) = Skip skipStart skipEnd hops
  where
  skipStart = etToConfig startPh $ unFlattenET $ tapeToVector startT
  (hops, simEnd) = simulateUntilCondition t (startPh, startT)
  dimV :: Natural
  dimV = natVal (Proxy @(Dim v))
  skipEnd :: SkipEnd Natural (v Bit)
  skipEnd = case simEnd of
    UnknownEdge e -> SkipUnknownEdge e
    FallRight ph ls -> SkipStepped ph $ Side R $ rle $ listToVector ls
    ReachedLeftMost ph p rs
      -> let
        (pointList, restRs) = splitAtExact (fromIntegral dimV - 1) rs
        point = V.fromList' (p : pointList)
        in
        SkipStepped ph $ Middle $ ExpTape [] point $ rle $ listToVector restRs
    --TODO: these numbers are wrong, as is >>
    CECycle n m -> SkipNonhaltProven $ Cycle (fromIntegral n) (fromIntegral m)
    Halts tape -> SkipHalt $ Middle $ unFlattenET tape

initVectorBook :: forall v. (Vector v Bit, Ord (v Bit), Pretty (v Bit)) => Turing -> SkipBook (v Bit)
initVectorBook t = appEndo (foldMap (Endo . addInitialSkipToBook) skips) Empty where
  skips = first FinCount . makeVectorSkip t <$> allInitTapes (natVal (Proxy @(Dim v))) t

--this pile of stuff is copied from the source code of fixed-vector and hacked together
--it is very possible it is somehow wrong
newtype instance MVec n s Bit = MV_Bool (P.MVec n s Word8)
newtype instance Vec  n   Bit = V_Bool  (P.Vec  n   Word8)

instance Arity n => Unbox n Bit

instance Arity n => MVector (MVec n) Bit where
  new          = MV_Bool `liftM` new
  {-# INLINE new         #-}
  copy (MV_Bool v) (MV_Bool w) = copy v w
  {-# INLINE copy        #-}
  move (MV_Bool v) (MV_Bool w) = move v w
  {-# INLINE move        #-}
  unsafeRead  (MV_Bool v) i   = toBit `liftM` unsafeRead v i
  {-# INLINE unsafeRead  #-}
  unsafeWrite (MV_Bool v) i b = unsafeWrite v i (fromBit b)
  {-# INLINE unsafeWrite #-}

instance Arity n => IVector (Vec n) Bit where
  unsafeFreeze (MV_Bool v) = V_Bool  `liftM` unsafeFreeze v
  unsafeThaw   (V_Bool  v) = MV_Bool `liftM` unsafeThaw   v
  unsafeIndex  (V_Bool  v) = toBit . unsafeIndex v
  {-# INLINE unsafeFreeze #-}
  {-# INLINE unsafeThaw   #-}
  {-# INLINE unsafeIndex  #-}


fromBit :: Bit -> Word8
{-# INLINE fromBit #-}
fromBit (Bit True) = 1
fromBit (Bit False) = 0

toBit :: Word8 -> Bit
{-# INLINE toBit #-}
toBit 0 = Bit False
toBit _ = Bit True

dispVecBit :: (Arity n) => Vec n Bit -> Text
dispVecBit v = "|" <> mconcat (dispBit <$> V.toList v) <> "|"

instance Arity n => Pretty (Vec n Bit) where
    pretty = pretty . dispVecBit

instance (Arity n) => TapeSymbol (Vec n Bit) where
  blank = V.replicate (Bit False)
  allSymbols = toList $ V.fromList <$> allBitsLengthN (natVal (Proxy @n))
  --for now, we're going with the "you're always on the left part of the symbol" take
  getPoint v = v ! 0
  toBits = V.toList
  fromBits l = let vecLen = fromIntegral $ natVal (Proxy @n) in
    if length l < vecLen then ([], l)
    else let (start, end) = splitAtExact vecLen l in
        first (V.fromList' start :) $ fromBits end
  initBook = initVectorBook


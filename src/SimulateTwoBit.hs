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
import Results
import Glue
import Simulate
import TapeSymbol
import Tape
import HaltProof (HaltProof(Cycle))
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


{-
simulateUntilCondition
for rightward transitions, we want either to fall off the right 
  or get to the leftmost bit on the tape
for leftward transitions, we want either to get to the leftmost bit on the tape, or the
  n-1th rightmost; but waiting until we fall off the right can't hurt much 
the natural is the number of hops it took, and the conditionend means:
Unknown: we hit an unknown edge
fallright: we fell off the right, here is the tape to our left
reachedleftmost: we're on the leftmost bit, here's the bit and the tape to our gith
cycle: the machine enters the same state in steps n and m 
  (here the stepcount natural is equal to n)
-}

data ConditionEnd = UnknownEdge Edge
                  | FallRight Phase [Bit]
                  | ReachedLeftMost Phase Bit [Bit]
                  | CECycle Natural Natural
                  | Halts (Tape Bit)

  deriving (Eq, Ord, Show, Generic)
instance NFData ConditionEnd
simulateUntilCondition :: Turing -> (Phase, Tape Bit) -> (Natural, ConditionEnd)
simulateUntilCondition t (ph, startTape) = loop startState 0 Empty where
  startState = TMState ph startTape
  loop :: TMState (Tape Bit) -> Natural -> Map (TMState (Tape Bit)) Natural
    -> (Natural, ConditionEnd)
  loop curState curStep pastStateMap = case pastStateMap ^. at curState of
    Just m -> (m, CECycle curStep m)
    Nothing -> let
      newMap = pastStateMap & at curState ?~ curStep
      newStep = curStep + 1
    --note that simStep right now does the wrong thing because at the end of 
    --the tape it assumes that there is an infinite bank of trues there but we 
    --want to fall off the end of the tape
     in case simStep t curState of
       Unknown e -> (curStep, UnknownEdge e)
       Stopped _ finalTape -> (newStep, Halts finalTape)
       Stepped _ newState@(TMState newPh newTape) -> case newTape of
         Tape [] p rs -> (newStep, ReachedLeftMost newPh p rs)
         _ -> loop newState newStep newMap

makeTwoBitSkip :: Turing -> (Phase, Tape Bit) -> Skip Natural TwoBit
makeTwoBitSkip t (startPh, startT) = Skip skipStart skipEnd hops
  where
  skipStart = etToConfig startPh $ etBitToTwoBit $ unFlattenET startT
  (hops, simEnd) = simulateUntilCondition t (startPh, startT)
  skipEnd = case simEnd of
    UnknownEdge e -> SkipUnknownEdge e
    FallRight ph ls -> SkipStepped ph $ Side R $ rle $ pairBitList ls
    ReachedLeftMost ph p (r : rs) 
      -> SkipStepped ph $ Middle $ ExpTape [] (TwoBit p r) $ rle $ pairBitList rs
    ReachedLeftMost {} -> error "unreachable maketwobitskip"
    --TODO: these numbers are wrong, as is >>
    CECycle n m -> SkipNonhaltProven $ Cycle (fromIntegral n) (fromIntegral m)
    Halts tape -> SkipHalt $ Middle $ unFlattenET tape

initTwoBitBook :: Turing -> SkipBook TwoBit 
initTwoBitBook t = appEndo (foldMap (Endo . addInitialSkipToBook) skips) Empty where 
  skips = first FinCount . makeTwoBitSkip t . second flattenET <$> allInitTapes t

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

flattenET :: ExpTape s Natural -> Tape s
flattenET (ExpTape ls p rs) = Tape (unRLE ls) p (unRLE rs)

unFlattenET :: (Eq s) => Tape s -> ExpTape s Natural
unFlattenET (Tape ls p rs) = ExpTape (rle ls) p (rle rs)

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

--the next thing to do to get this working is to make the `initskips` thing in simulate
--polymorphic, and to start piping through the polymorphism more, as before, to be able
--to do the usual simulation type stuff but with Twobit
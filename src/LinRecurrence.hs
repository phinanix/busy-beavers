module LinRecurrence where 


import Relude
import Control.Lens
import Data.Map.Monoidal (assocs, keysSet)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter
import Data.Either.Combinators

import Data.Bits (Bits(bit))
import Data.List (minimumBy, findIndex)
import qualified Data.List.NonEmpty as NE
import Relude.Extra (bimapBoth)
import Relude.Foldable (Bitraversable)
import qualified Relude.Unsafe as Unsafe

import Control.Exception (assert)
import Relude.Unsafe ((!!))
import qualified Relude.Unsafe as U
import Data.Bifoldable (Bifoldable)


import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
import HaltProof
import TapeSymbol
import Safe.Partial

--given a list, sorts it and uses this to find whether it contains a duplicate
hasPair :: (Ord a) => [a] -> Maybe (Int, Int)
hasPair [] = Nothing
hasPair xs = let 
    enumXs = zip [0,1..] xs 
    sortedXs = sortOn snd enumXs 
    xsPairs = zip (U.init sortedXs) (U.tail sortedXs)
    in 
    --find the first element of the list where the two things are equal
    --then return their indices
    (\((i, _a), (j, _b)) -> (i,j)) <$> 
      find (\((_i, a), (_j, b)) -> a==b) xsPairs


--works by sorting the history, determining if there is a duplicate, 
--and if so, there is a cycle and we can return a haltproof right away
histHasDuplicate :: (Ord s, Ord c) => ReverseTapeHist s c -> Maybe (HaltProof s)
histHasDuplicate (ReverseTapeHist revHist) = mkHP <$> hasPair (reverse revHist) 
  where
    mkHP (i, j) = Cycle i j


-- a region of the tape extending some leftwards and some rightwards
-- the first int is non-positive and expresses the leftward extent
-- the second int is non-negative and expresses the rightward extent
data TapeRegion = UnsafeTapeRegion Int Int deriving (Eq, Ord, Show, Generic) 
instance NFData TapeRegion 

mkTapeRegion :: HasCallStack => Int -> Int -> TapeRegion
mkTapeRegion l r = assertMsg (l<=r) ("l,r" <> show l <> " " <> show r) UnsafeTapeRegion l r 

liveRegion :: (TapeSymbol s) => [(s, InfCount)] -> Int 
liveRegion xs = case xs of 
  [] -> error "empty tape"
  (x : xs) -> let 
    neXs = x :| xs
    lastSym = last neXs 
    liveSyms = init neXs
    in let 
      ans = assert (lastSym == (blank, Infinity)) 
        (case viaNonEmpty last liveSyms of 
          Nothing -> id
          Just (s, _c) -> assert (s /= blank)
        )
        sum $ infCountToInt . snd <$> liveSyms 
      in 
        assert (ans >= 0) ans 

liveTapeRegion :: (TapeSymbol s) => ExpTape s InfCount -> TapeRegion
liveTapeRegion (ExpTape ls _p rs) = mkTapeRegion (- (liveRegion ls)) (liveRegion rs)

intersectRegions :: TapeRegion -> TapeRegion -> TapeRegion
intersectRegions (UnsafeTapeRegion l r) (UnsafeTapeRegion l' r') 
  = mkTapeRegion (max l l') (min r r')

subsetRegion :: TapeRegion -> TapeRegion -> Bool 
subsetRegion (UnsafeTapeRegion l r) (UnsafeTapeRegion l' r') = (l >= l') && (r <= r')

-- a - b = bits of a which are not in b, or nothing if they are equal
subtractRegions :: TapeRegion -> TapeRegion -> Maybe TapeRegion 
subtractRegions a@(UnsafeTapeRegion l r) b@(UnsafeTapeRegion l' r') = 
  assertMsg (r - l == r' - l') "" $ case compare l l' of
    LT -> Just $  UnsafeTapeRegion l (l'-1) 
    EQ -> Nothing 
    GT -> Just $ UnsafeTapeRegion (r' + 1) r 

--detects lin recurrence, as determined by the history
--currently disphist is implemented in a bad way (skips can care about a whole chunk of symbols) so 
--this function isn't actually writeable, so I should fix that first 

{- Plan for LinRecur 30 Jan 22:
There is a type called ReadShift, that contains 3 ints (l, r, s). 
applying a skip corresponds to an RS, where (l, r) corresponds to the 
inclusive range of bits the skip consumes (neg left, pos right, 0 current 
head pos), and s is the amount that the machine shifts left or right after 
the skip is done being applied. l <= r always. 

ReadShift is a monoid: applying two skips in a row is always congruent to a 
particular other skip, which has its own ReadShift. To compose two ReadShifts,
first, you shift the second one's l and r into the first one's "frame of 
reference" by adding the first one's shift to l and r. Now, you have an l from
the first one and the second one, and you take the max, and the same for r. 
For s, you simply add them together. 
Mempty is simply all 0. 

To detect whether a recurrence exists between history point i and j, you need
3 things: the ReadShift corresponding to the sum of all the readshifts from
i to j, the tape at i and the tape at j. The ReadShift tells you which chunk
of the tape at i affected the progression of the machine as it went through 
to step j. You grab that width of tape at the start and at 
the end, if they are the same, then you have found a recurrence. 

To find a readshift from a skip, the l and the r are simply the length of 
each half of the config you start with. The shift is the difference between 
the length of l at the start and the length of l at the end (which for 
a correctness check should be the same as the negative difference for the 
same for r). There's a mild bit of fuckiness if you fall off the tape rather
than ending in the middle.

Functions to write / things to do:
Function which given two tapes and a readshift computes the possibility of 
  recurrence (checkForRecur)
Function which given two numbers and the two histories extracts the two 
  tapes and the readshift and hands it to the preceeding function
  (checkForRecurAtIndices)
Outer loop which calls the preceeding function with all combinations of two 
  numbers which are valid (in order; ie it should do (1,2) through (n-1, n) 
  then (1, 3) and so on increasing the common difference each time)
--Type definition and monoid instance on ReadShift
Function which takes a skip and gives you its ReadShift
Update SimulateState to track readshifts in RSHist 
(unsure) update other things which use DispHist to use RSHist

New design of readshift 
-}

detectLinRecurrence :: forall s. (HasCallStack, TapeSymbol s, Pretty s) 
  => TapeHist s InfCount 
  -> ReadShiftHist 
  -> Maybe (HaltProof s)
detectLinRecurrence hist@(TapeHist thList) rshist@(ReadShiftHist rshList) 
  = --trace ("len hist: " <> show (length thList) <> " recent tape " <> showP (Unsafe.last thList)) $ 
    viaNonEmpty head $ catMaybes allMaybeProofs
  where
  --i and j are inclusive, in a sense, but that means we want to index into rshList in an 
  -- (incl., excl.) way, 
  checkForRecurAtIndices :: (Int, Int) -> Maybe (HaltProof s)
  checkForRecurAtIndices (i, j) = let 
      ans = checkForRecur (i, j) startC endC readShift 
      showMsg = if has _Just ans then trace ("found proof. indices " 
        <> show i <> "," <> show j <> "\ntape1:\n"
        <> showP startC <> "\ntape2:\n" <> showP endC
         <> "\nreadShift:\n" <> showP readShift <> 
        "\nfrom list\n" <> showP (slice i (j-1) rshList))
      else id
    in 
    showMsg
     ans 
    where 
    startC = thList !! fromIntegral i
    endC = thList !! fromIntegral j 
    readShift = neMConcat $ fromJust $ nonEmpty $ slice i (j-1) rshList 
  --lenHist is the length of the history, so it minus one is max valid index
  genValidIndices :: Int -> [(Int, Int)]
  genValidIndices lenHist = concat $ genIndicesAtDist lenHist <$> [1, 2 .. lenHist -1]
  genIndicesAtDist :: Int -> Int -> [(Int, Int)]
  genIndicesAtDist lenHist dist 
    = (\x -> (x, x + dist)) <$> [0, 1 .. (lenHist -1) - dist] 
  allMaybeProofs = let msg = "lengths:" <> show (length thList, length rshList)
    in 
    --trace msg $ 
    assert (length thList - 1 == length rshList) $ 
    checkForRecurAtIndices <$> genValidIndices (fromIntegral $ length thList)

--alg 3 oct: anything read which is outside of the written region must be F (todo check)
checkForRecur :: (Partial, TapeSymbol s) 
  => (Int, Int)
  -> (Phase, ExpTape s InfCount) 
  -> (Phase, ExpTape s InfCount) 
  -> ReadShift -> Maybe (HaltProof s)
checkForRecur (i,j) 
  (ph, et@(ExpTape _ls p _rs)) 
  (ph', et'@(ExpTape _ls' p' _rs'))
  (ReadShift l r s) = do 
    guard (ph == ph')
    guard (p == p') --TODO unnecessary? 
    
    --TODO crashes if range does not include 0. but maybe that's actually correct
    let startRng = sliceExpTape et l r 
        endRng = sliceExpTape et' l r
    guard (startRng == endRng) 
    -- here's where we need to add the new code to check - we need to check that the 
    -- range the end is reading from intersected with the part of the tape that's live 
    -- at the endrange step is a subrange of the range we wrote via the start range
    -- which is the start range shifted by the readshift
    let writtenRng = trace ("l " <> show l <> " r " <> show r <> " s " <> show s) 
          mkTapeRegion (l - s) (r - s)
        readRng = mkTapeRegion l r
        liveAtEndRng = liveTapeRegion et' 
    trace ("written " <> show writtenRng <> " read " <> show readRng 
          <> " live at end " <> show liveAtEndRng) 
      guard $ (readRng `intersectRegions` liveAtEndRng) `subsetRegion` writtenRng 
    pure $ LinRecur i j
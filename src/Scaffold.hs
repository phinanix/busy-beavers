module Scaffold where

import Relude
import qualified Relude.Unsafe as U
import Control.Lens
import Prettyprinter
import Control.Exception (assert)
import Data.List (minimum, maximum) 

import qualified Data.List.NonEmpty as NE 
import qualified Data.Map as M
import qualified Data.Set as S

import Turing
import Count
import Results
import SimulateSkip
import Skip
import Induction
import SimulationLoops
import TapeSymbol
import ExpTape
import Util 
import Safe.Exact
import Relude.Extra (bimapBoth)


{-
- how to turn a scaffold into a set of proof goals: 
1) find the common prefixes and suffixes of the characters the traces contain
2) filter down to the points where the machine is at the furthest left or right it 
   gets (RLE-wise)
3) for now, try all pairs of 1 thing from prefix & 1 thing from suffix
4) given a set of history pairs, generalize it similarly to guessWhatHappensNext 
5) attempt to prove it via induction
6) once at least 1 induction succeeds, go back to trying to prove the full runForever 
   without induction

this won't get everything, but it should get all the counters and plausibly other things
-}

obtainMachineConfigs :: forall s. (TapeSymbol s) => Int -> Turing
  -> Either Text (Phase,  [(Int, (Phase, ExpTape s InfCount))])
obtainMachineConfigs = (obtainCriticalIndicesConfigs . fst) .: getTwoHistAfterTime

obtainHistorySlices :: forall s. (TapeSymbol s) => Int -> Turing
  -> Either Text (NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)]))
obtainHistorySlices limit m = do
  let (th@(TapeHist tapeHist), ReadShiftHist readShiftHist) = getTwoHistAfterTime limit m
      labelledTapeHist = zip [0, 1..] tapeHist
  machineConfigs <- obtainCriticalIndicesConfigs th
  -- TODO: trying drop 1 to fix startup effects
  let indices = drop 1 $ fst <$> snd machineConfigs
      pairedIndices = zip (U.init indices) (U.tail indices)
  nonemptyPairs <- failMsg (error "pairs were empty") $ nonEmpty pairedIndices
  pure $ (\(s, e) -> (s, e, (\((w, (x, y)), z) -> (w, x, y, z)) <$> zip (slice s e labelledTapeHist) (slice s e readShiftHist)))
        <$> nonemptyPairs

obtainSigsWhichOccur :: (Ord s) => NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)])
 -> Set (Phase, Signature s)
obtainSigsWhichOccur = intersectFold
  . fmap (S.fromList . fmap makePhaseSig . getThird)
  where
  getThird (_a, _b, c) = c
  makePhaseSig (_s, ph, tape, _rs) = (ph, tapeSignature tape)

instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where 
  pretty (a, b, c, d) = "(" <> pretty a <> ", "
   <> pretty b <> ", " 
   <> pretty c <> ", "
   <> pretty d <> ")"

instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e) => Pretty (a, b, c, d, e) where 
  pretty (a, b, c, d, e) = "(" <> pretty a <> ", "
   <> pretty b <> ", " 
   <> pretty c <> ", "
   <> pretty d <> ", "   
   <> pretty e <> ")"   

numToLet :: Int -> Char
numToLet i = ab U.!! i where 
  ab = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

filteredHistories :: forall s. (TapeSymbol s) => Int -> Turing
  -> Either Text (NonEmpty (Int, Int, [(Char, Int, Phase, ExpTape s InfCount, ReadShift)]))
filteredHistories limit m = do 
  historySlices <- obtainHistorySlices limit m 
  let sigsWhichOccurred = obtainSigsWhichOccur historySlices 
      sigsToLetters = M.fromList . fmap (second numToLet) . flip zip [0, 1..] .  S.toList $ sigsWhichOccurred
      third f (x, y, z) = (x, y, f z)
      filteredHist = third (mapMaybe (\(s, ph, tape, rs) 
        -> case sigsToLetters ^. at (ph, tapeSignature tape) of 
          Nothing -> Nothing 
          Just ch -> Just (ch, s, ph, tape, rs) 
        ))
        <$> historySlices 
  trace ("sigs to letters: " <> showP (M.assocs sigsToLetters)) $ pure filteredHist 
  

commonPrefix :: NonEmpty [Char] -> [Char] 
commonPrefix strings = takeExact lastValid $ head strings where 
    longestStringLen = maximum1Of traverse1 $ length <$> strings 
    isValid i = allEqual $ toList $ takeExact i <$> strings 
    lastValid = U.last $ takeWhile isValid [0.. longestStringLen]

scaffoldHypotheses :: forall s. (TapeSymbol s) 
    => NonEmpty (Int, Int, [(Char, Int, Phase, ExpTape s InfCount, ReadShift)])
    -> NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)])
    -> [Skip Count s]
scaffoldHypotheses filteredHist unfilteredHist 
  = theAssert $ mapMaybe rightToMaybe $ toList generalizedHistories 
  where 
    alphabets = (\(_a,_b,c) -> c) <$> ((\(a,_b,_c,_d, _e) -> a) <$$$> filteredHist)
    prefix = commonPrefix alphabets 
    suffix = reverse $ commonPrefix $ reverse <$> alphabets
    prefixSuffixPairs :: NonEmpty (Int, Int, 
        [(Char, Int, Phase, ExpTape s InfCount, ReadShift)], 
        [(Char, Int, Phase, ExpTape s InfCount, ReadShift)])
    prefixSuffixPairs = (\(x,y,z) -> (x, y, takeExact (length prefix) z, 
        reverse $ takeExact (length suffix) $ reverse z)) 
        <$> filteredHist
    (_s, _e, pref, suf) = head prefixSuffixPairs 
    --yes, we are deliberately counting the number of (s, Count) pairs rather than the number of s 
    minLeftLen = minimum $ (\(_, _, _, ExpTape ls _p _rs, _) -> length ls) <$> (pref ++ suf)
    minRightLen = minimum $ (\(_, _, _, ExpTape _ls _p rs, _) -> length rs) <$> (pref ++ suf)
    etLRMost (ExpTape ls _p rs) = length ls == minLeftLen || length rs == minRightLen
    lrmostPrefixSuffixes = (\f (w, x, y, z) -> (w, x, f y, f z)) (filter (etLRMost . view _4)) 
        <$> prefixSuffixPairs
    theAssert = let thing = (\(_, _, p, s) -> (view _1 <$> p, view _1 <$> s)) <$> lrmostPrefixSuffixes in 
        assert $ allEqual $ toList thing
    

    makePair s e = (\(_, _, ps, ss) -> (ps U.!! s, ss U.!! e)) <$> prefixSuffixPairs
    makeGuessHist :: Int -> Int -> NonEmpty (Natural, [(Phase, ExpTape s InfCount)], [ReadShift])
    makeGuessHist s e = fmap (\(x, (y, z)) -> (x, y, z)) . NE.zip (3 :| [4,5..]) 
      $ munge4 . sliceHist <$> histIndexPairs 
      where 
        listOfPairs = makePair s e 
        indexPairs = bimapBoth (view _2) <$> listOfPairs 
        histIndexPairs = neZipExact indexPairs (view _3 <$> unfilteredHist) 
        sliceHist ((s, e), hist) = slice s e hist 
        munge4 :: [(a,b,c,d)] -> ([(b,c)],[d])
        munge4 = foldr (\(_a,b,c,d) (bcs, ds) -> ((b,c):bcs, d:ds)) ([],[])
    --this is a list of guesses. where each guess is a nonempty list of the example
    --histories we've seen corresponding to that guess. 
    guessHists = makeGuessHist <$> [0, 1.. length (lrmostPrefixSuffixes ^. ix 0 . _3)] 
        <*> [0, 1.. length (lrmostPrefixSuffixes ^. ix 0 . _4)]
    generalizedHistories = generalizeHistories <$> guessHists 
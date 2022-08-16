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

obtainHistorySlices' :: forall s. (TapeSymbol s) => Int -> Turing
  -> Either Text (NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)]))
obtainHistorySlices' limit m = let (th, rsh) = getTwoHistAfterTime limit m in 
  obtainHistorySlices th rsh


obtainHistorySlices  :: forall s. (TapeSymbol s) => TapeHist s InfCount -> ReadShiftHist
  -> Either Text (NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)]))
obtainHistorySlices th@(TapeHist tapeHist) (ReadShiftHist readShiftHist) = do 
  let labelledTapeHist = zip [0, 1..] tapeHist
  machineConfigs <- obtainCriticalIndicesConfigs th
  -- TODO: trying drop 1 to fix startup effects
  let indices = drop 1 $ fst <$> snd machineConfigs
      pairedIndices = zip (U.init indices) (U.tail indices)
  nonemptyPairs <- trace ("pairedIndices" <> show pairedIndices <> "length" <> show (length labelledTapeHist) <> show (length readShiftHist) ) 
    failMsg (error "pairs were empty") $ nonEmpty pairedIndices
  --remember, the readshifts go between the tapes in the tapehist, so there is one less of them
  pure $ (\(s, e) -> (s, e, (\((w, (x, y)), z) -> (w, x, y, z)) <$> zip (slice s e labelledTapeHist) (slice s (e-1) readShiftHist)))
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

-- todo this is great for debugging but pretty dumb that we keep exceeding the length limit
numToLet :: Int -> Char
numToLet i = ab !!! i where 
  ab = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

newtype SigID = SigID Int deriving (Eq, Ord, Show)
instance Pretty SigID where 
  pretty (SigID s) = if s < 52 then pretty (numToLet s) else pretty s

filterHistories' :: forall s. (TapeSymbol s) => Int -> Turing
  -> Either Text (NonEmpty (Int, Int, [(SigID, Int, Phase, ExpTape s InfCount, ReadShift)]))
filterHistories' limit m = do 
  historySlices <- obtainHistorySlices' limit m 
  pure $ filterHistories historySlices 
  
filterHistories :: Ord s
  => NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)])
  -> NonEmpty (Int, Int, [(SigID, Int, Phase, ExpTape s InfCount, ReadShift)])
filterHistories historySlices =   
  let sigsWhichOccurred = obtainSigsWhichOccur historySlices 
      sigsToLetters = M.fromList . fmap (second SigID) . flip zip [0, 1..] .  S.toList $ sigsWhichOccurred
      third f (x, y, z) = (x, y, f z)
      filteredHist = third (mapMaybe (\(s, ph, tape, rs) 
        -> case sigsToLetters ^. at (ph, tapeSignature tape) of 
          Nothing -> Nothing 
          Just ch -> Just (ch, s, ph, tape, rs) 
        ))
        <$> historySlices 
  in 
    filteredHist 


commonPrefix :: (Eq a) => NonEmpty [a] -> [a] 
commonPrefix strings = takeExact lastValid $ head strings where 
    longestStringLen = maximum1Of traverse1 $ length <$> strings 
    isValid i = allEqual $ toList $ takeExact i <$> strings 
    lastValid = U.last $ takeWhile isValid [0.. longestStringLen]

makeScaffoldHypotheses :: forall s. (TapeSymbol s) 
    => NonEmpty (Int, Int, [(SigID, Int, Phase, ExpTape s InfCount, ReadShift)])
    -> NonEmpty (Int, Int, [(Int, Phase, ExpTape s InfCount, ReadShift)])
    -> [Skip Count s]
makeScaffoldHypotheses filteredHist unfilteredHist 
  = theAssert $ mapMaybe rightToMaybe $ toList generalizedHistories 
  where 
    alphabets = (\(_a,_b,c) -> c) <$> ((\(a,_b,_c,_d, _e) -> a) <$$$> filteredHist)
    prefix = commonPrefix alphabets 
    suffix = reverse $ commonPrefix $ reverse <$> alphabets
    prefixSuffixPairs :: NonEmpty (Int, Int, 
        [(SigID, Int, Phase, ExpTape s InfCount, ReadShift)], 
        [(SigID, Int, Phase, ExpTape s InfCount, ReadShift)])
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
    theAssert = let thing = (\(_, _, p, s) -> (view _1 <$> p, view _1 <$> s)) 
                     <$> lrmostPrefixSuffixes in 
        assert $ allEqual $ toList thing
    
    --this is not always a valid pair, because the start could've occured after the end, eg 20,19
    -- so we need to check that what we're acquiring with !!! satisfies start <= end and then we'll 
    -- be good 
    --makePair :: Int -> Int -> 
    makePair s e = (\(_, _, ps, ss) -> case (ps !!! s, ss !!! e) of 
      (x@(_, s_step, _, _, _), y@(_, e_step, _, _, _)) -> 
        if s_step <= e_step then Just (x, y) else Nothing 
      ) <%> lrmostPrefixSuffixes
    makeGuessHist :: Int -> Int -> Maybe (NonEmpty (Natural, [(Phase, ExpTape s InfCount)], [ReadShift]))
    makeGuessHist s e = fmap (\(x, (y, z)) -> (x, y, z)) . NE.zip (3 :| [4,5..]) 
      $ munge4 . sliceHist <$> histIndexPairs 
      where 
        listOfPairs = makePair s e 
        indexPairs = --trace ("list of pairs:" <> showP listOfPairs) 
          bimapBoth (view _2) <$> listOfPairs 
        histIndexPairs = neZipExact indexPairs unfilteredHist
        sliceHist ((slice_start, slice_end), (hist_start, hist_end, hist)) = 
          trace ("slice-ing" <> show (slice_start, slice_end) <> show (hist_start, hist_end))
          slice (slice_start - hist_start) (slice_end - hist_start) hist 
        munge4 :: [(a,b,c,d)] -> ([(b,c)],[d])
        munge4 = foldr (\(_a,b,c,d) (bcs, ds) -> ((b,c):bcs, d:ds)) ([],[])
    --this is a list of guesses. where each guess is a nonempty list of the example
    --histories we've seen corresponding to that guess. 
    guessHists = trace (showP lrmostPrefixSuffixes) 
      makeGuessHist <$> [0, 1.. length (lrmostPrefixSuffixes ^. ix 0 . _3) - 1] 
        <*> [0, 1.. length (lrmostPrefixSuffixes ^. ix 0 . _4) - 1]
    generalizedHistories = generalizeHistories <$> guessHists 
 
proveByScaffold :: forall s. (TapeSymbol s) => Turing -> SkipBook s 
    -> TapeHist s InfCount -> ReadShiftHist 
    -> Either Text (Skip Count s, SkipOrigin s) 
proveByScaffold machine book th rsh = do 
    unfilteredHistories <- obtainHistorySlices th rsh 
    let filteredHistories = filterHistories unfilteredHistories
        scaffoldHypothesis = makeScaffoldHypotheses filteredHistories unfilteredHistories
        mbProofs =
            (\s -> rightToMaybe $ (s,) <$> proveInductively 110 machine book s (getVar s)) 
            <$> scaffoldHypothesis
    failMsg "no proof succeeded" $ viaNonEmpty head $ catMaybes mbProofs
    
    where 
      getVar :: Skip Count s -> BoundVar 
      getVar skip = let bvs = getBoundVars skip in 
        -- (if length bvs > 1 
        --     then trace ("machine: " <> showP machine <> "skip:" <> showP skip 
        --                 <> "bvs:" <> show bvs) 
        --     else id) 
        U.head bvs 
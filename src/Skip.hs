module Skip where

import Relude hiding (mapMaybe)
import Control.Lens
import Data.Witherable

import Turing
import Count
import Util

-- --a data-type used for matching up skips where the type can be wild
-- data Wild a = Wild | NotWild a deriving (Eq, Ord, Show)
--
-- --a Wild matches any value of type a while a Specific only matches that value
-- matchEq :: (Eq a) => Wild a -> Wild a -> Bool
-- matchEq Wild _ = True
-- matchEq _ Wild = True
-- matchEq (NotWild a) (NotWild b) = a == b

data Config s = Config
  { _cstate :: Phase
  , _ls :: [(s, Count)]
  , _c_point :: (s, Count, Dir)
  , _rs :: [(s, Count)]
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (Config s)

--TODO:: make skips use Wild - it's a lot trickier than I thought
data Skip s = Skip
  { _start :: Config s
  , _end :: Config s
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (Skip s)

$(makeLenses ''Config)
$(makeLenses ''Skip)

--a Perfect match had no leftovers
--or we might have used up all of the skip and had some tape leftover, or vv
data HeadMatch s = PerfectH | TapeHLeft (s, Count) deriving (Eq, Ord, Show)

--we take the start of a skip and the start of a tape, and return Nothing if they
--don't match, and the match if they do
matchTapeHeads :: (Eq s) => (s, Count) -> (s, Count) -> EquationState (HeadMatch s)
matchTapeHeads (sb, skipC) (tb, tapeC) | sb == tb = matchCount skipC tapeC >>= \case
    Empty -> pure PerfectH
    newCount -> pure (TapeHLeft (tb, newCount))
--if the bits fail to match, the match fails all together
matchTapeHeads _ _ = nothingES

--when you match a skip and a tape, either they perfectly annihilate, the tape
--has at least one thing left, or the skip matches the whole tape and has at least
--one thing left
data TapeMatch s = Perfect | TapeLeft (NonEmpty (s, Count)) | SkipLeft (NonEmpty (s, Count)) deriving (Eq, Ord, Show)
--TODO:: maybe define a pattern synonym for TapeMatch that either returns a (possibly empty)
--leftover tape or the skip

--note: this routine does not make advantage of the fact that the ExpTape has the invariant
--that there are never two adjacent blocks with the same symbol - it pessimistically assumes
--that may not be the case
--given a skip to match against a tape, returns the remaining tape that's left after consuming
--all the tape that matches the skip, the rest of the unmatched skip, or
--fails, returning nothing
--example :: matchBitTape [(F, 2), (T, 1)] [(F, 2), (T, 3), (F, x)] == [(T, 2), (F, x)]
--returns Nothing if the match fails, else the match
matchTape :: (Eq s) => [(s, Count)] -> [(s, Count)] -> EquationState (TapeMatch s)
matchTape [] [] = pure Perfect
matchTape [] (t:ts) = pure $ TapeLeft (t :| ts)
matchTape (s:rest) []  = pure $ SkipLeft (s :| rest)
--else we can match the heads
matchTape (skipHead:restSkip) (tapeHead:restTape) = matchTapeHeads skipHead tapeHead >>= \case
  --if the heads perfectly square off, we can just recurse
  PerfectH -> matchTape restSkip restTape
  --else we have a leftover bit of tape and match against it
  --TODO:: I think we can short circuit and skip the rest of the match here if the skip has the invariant
  (TapeHLeft tapeHead) -> matchTape restSkip (tapeHead:restTape)

data TapeOrInf s = Infinite | NewTape [(s, Count)] deriving (Eq, Ord, Show, Generic)

--specializes matchTape to Bit, allowing the routine to
--signal the skip will match an infinite amount of tape
--fails if there is skip left-over
--first line is some seriously ugly munging but I'm not sure off the top of my head how to do better
--the function's type is (a -> Maybe b) -> Maybe (a,c) -> Maybe (b,c)
matchBitTape :: [(Bit, Count)] -> [(Bit, Count)] -> EquationState (TapeOrInf Bit)
matchBitTape skip tape = mapMaybe matchToTapeOrInf $ matchTape skip tape where
  matchToTapeOrInf :: TapeMatch Bit -> Maybe (TapeOrInf Bit)
  matchToTapeOrInf = \case
    Perfect -> pure $ NewTape []
    TapeLeft (toList -> newTape) -> Just $ NewTape newTape
    --if there's a count without any foralls, like a+3 where a is free, then
    --it just matches the infinite zeros
    SkipLeft ((False, Count _ _ Empty) :| []) -> Just $ NewTape []
    -- _notEmpty thereby must have foralls, and thus it matches the whole infinite
    -- rest of the tape
    SkipLeft ((False, _notEmpty) :| []) -> Just Infinite
    SkipLeft _ -> Nothing

--if you match two points, either they match perfectly, or some symbols of some count
--remain on one side
data PointMatch s = PerfectP | Lremains (s, Count) | Rremains (s, Count) deriving (Eq, Ord, Show, Generic)

matchPoints :: (Eq s) => (s, Count, Dir) -> (s, Count, Dir) -> EquationState (PointMatch s)
matchPoints (skipS, skipC, skipD) (tapeS, pointC, tapeD)
  | (skipS == tapeS) && (skipD == tapeD)
  = matchCount skipC pointC >>= \case --passing through the maybe
      Empty -> pure PerfectP
      --if some of the tape's point is not matched, then it remains on the tape
      --if we start matching from the right, the unmatched point is on the left
      remainC -> case mirrorDir tapeD of
        L -> pure $ Lremains (tapeS, remainC)
        R -> pure $ Rremains (tapeS, remainC)
-- matchPoints (skipS, skipC, skipD) (tapeS, pointC, tapeD) | (skipS == tapeS) = error ""
-- matchPoints (skipS, skipC, skipD) (tapeS, pointC, tapeD) | (skipD == tapeD) = error ""
matchPoints _ _ = nothingES

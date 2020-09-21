module Skip where

import Relude
import Control.Lens

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
matchTapeHeads :: (Eq s) => (s, Count) -> (s, Count) -> Maybe (HeadMatch s, (Count, Count))
matchTapeHeads (sb, skipC) (tb, tapeC) | sb == tb = matchCount skipC tapeC >>= \case
  Empty -> Just (PerfectH, (skipC, tapeC))
  newCount -> Just $ (TapeHLeft (tb, newCount), (skipC, tapeC))
--if the bits fail to match, the match fails all together
matchTapeHeads _ _ = Nothing

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
matchTape :: (Eq s) => [(s, Count)] -> [(s, Count)] -> Maybe (TapeMatch s, Map Count Count)
matchTape [] [] = Just $ (Perfect, Empty)
matchTape [] (t:ts) = Just $ (TapeLeft (t :| ts), Empty)
matchTape (s:rest) []  = Just $ (SkipLeft (s :| rest), Empty)
--else we can match the heads
matchTape (skipHead:restSkip) (tapeHead:restTape) = case matchTapeHeads skipHead tapeHead of
  --if the heads don't match, the whole match fails
  Nothing -> Nothing
  --if the heads perfectly square off, we can just recurse
  Just (PerfectH, eqn) -> matchTape restSkip restTape >>= traverse (addEquation eqn) where
  --else we have a leftover bit of tape and match against it
  --TODO:: I think we can short circuit and skip the rest of the match here if the skip has the invariant
  Just (TapeHLeft tapeHead, eqn) -> matchTape restSkip (tapeHead:restTape) >>= traverse (addEquation eqn)

data TapeOrInf s = Infinite | NewTape [(s, Count)]

--specializes matchTape to Bit, allowing the routine to
--signal the skip will match an infinite amount of tape
--fails if there is skip left-over
--first line is some seriously ugly munging but I'm not sure off the top of my head how to do better
--the function's type is (a -> Maybe b) -> Maybe (a,c) -> Maybe (b,c)
matchBitTape :: [(Bit, Count)] -> [(Bit, Count)] -> Maybe (TapeOrInf Bit, Map Count Count)
matchBitTape skip tape = bind (bitraverse matchToTapeOrInf pure) $ matchTape skip tape where
  matchToTapeOrInf :: TapeMatch Bit -> Maybe (TapeOrInf Bit)
  matchToTapeOrInf = \case
    Perfect -> Just $ NewTape []
    TapeLeft (toList -> newTape) -> Just $ NewTape newTape
    SkipLeft ((False, Count _ Empty) :| []) -> Just $ NewTape []
    SkipLeft ((False, _notEmpty) :| []) -> Just Infinite
    SkipLeft _ -> Nothing

--if you match two points, either they match perfectly, or some symbols of some count
--remain on one side
data PointMatch s = PerfectP | Lremains (s, Count) | Rremains (s, Count)

matchPoints :: (Eq s) => (s, Count, Dir) -> (s, Count, Dir) -> Maybe (PointMatch s, (Count, Count))
matchPoints (skipS, skipC, skipD) (tapeS, pointC, tapeD)
  | (skipS == tapeS) && (skipD == tapeD)
  = (, (skipC, pointC)) <$> (matchCount skipC pointC >>= \case --passing through the maybe
      Empty -> Just PerfectP
      --if some of the tape's point is not matched, then it remains on the tape
      --if we start matching from the right, the unmatched point is on the left
      remainC -> case mirrorDir tapeD of
        L -> Just $ Lremains (tapeS, remainC)
        R -> Just $ Rremains (tapeS, remainC))
matchPoints _ _ = Nothing
--
-- -- generalizePoint :: (s, Int, Dir) -> (s, Count, Dir)
-- -- generalizePoint (s, i, d) = (s, Specific i, d)

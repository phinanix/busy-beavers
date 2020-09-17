module Skip where

import Relude
import Control.Lens

import Turing
import Tape hiding (point)
import ExpTape hiding (point)

--a data-type used for matching up skips where the type can be wild
data Wild a = Wild | NotWild a deriving (Eq, Ord, Show)

--a Wild matches any value of type a while a Specific only matches that value
matchEq :: (Eq a) => Wild a -> Wild a -> Bool
matchEq Wild _ = True
matchEq _ Wild = True
matchEq (NotWild a) (NotWild b) = a == b

--a specific value is 7, a variable is x + 7, where the x is implicit
data Count = Specific Int | Xplus Int deriving (Eq, Ord, Show)

data Config s = Config
  { _cstate :: Phase
  , _ls :: [(Wild s, Count)]
  , _point :: (Wild s, Count, Wild Dir)
  , _rs :: [(Wild s, Count)]
  } deriving (Eq, Ord, Show)

data Skip s = Skip
  { _start :: Config s
  , _end :: Config s
  } deriving (Eq, Ord, Show)


$(makeLenses ''Config)
$(makeLenses ''Skip)

data CountMatch = PerfectCount | FirstRemain Count | SecondRemain Count

--not commutative - this is asking, we're trying to apply the count on the left to the count on the right
--does it work?
-- x will match any specific count, like 8, and any xplus, like x+1
matchCount :: Count -> Count -> Maybe CountMatch
matchCount (Specific i) (Specific j) = case compare i j of
  LT -> Just $ SecondRemain (Specific (j - i))
  EQ -> Just PerfectCount
  GT -> Just $ FirstRemain (Specific (i - j))
matchCount (Xplus i) (Specific j) = if i <= j
  then Just PerfectCount
  else Just $ FirstRemain (Xplus (i - j))
--a Specific can never consume more than the finite tail of an Xplus
matchCount (Specific i) (Xplus j) = Just $ SecondRemain $ Xplus (max 0 (j - i))
--a smaller or equal first value can expand to eat the whole second one
--eg x matches x + 10
--but if you try to apply x + 10 to x
--uh. I guess it fails? like x could be 1 or 9 and you can't return that
--weird that it's the only failure case. And it's only a partial failure - if you're
--trying to match x + 2 against x, you sort of "solve all the cases" except x = 1 or 2
--so there is finite work leftover. But I don't think we're going to handle that case right
--now
matchCount (Xplus i) (Xplus j) = if i <= j
  then Just PerfectCount
  else Nothing
  
--a Perfect match had no leftovers
--or we might have used up all of the tape and had some skip leftover, or vv
data HeadMatch s = PerfectH | SkipHLeft (Wild s, Count) | TapeHLeft (s, Count) deriving (Eq, Ord, Show)

--we take the start of a skip and the start of a tape, and return Nothing if they
--don't match, and the match if they do
matchTapeHeads :: (Eq s) => (Wild s, Count) -> (s, Count) -> Maybe (HeadMatch s)
matchTapeHeads (wb, skipC) (bit, tapeC) | wb `matchEq` (NotWild bit) = matchCount skipC tapeC >>= \case
  PerfectCount -> Just PerfectH
  FirstRemain c -> Just $ SkipHLeft (wb, c)
  SecondRemain c -> Just $ TapeHLeft (bit, c)
--if the bits fail to match, the match fails all together
matchTapeHeads _ _ = Nothing

--when you match a skip and a tape, either they perfectly annihilate, the tape
--has at least one thing left, or the skip matches the whole tape and has at least
--one thing left
data TapeMatch s = Perfect | TapeLeft (NonEmpty (s, Count)) | SkipLeft (NonEmpty (Wild s, Count))

--note: this routine does not make advantage of the fact that the ExpTape has the invariant
--that there are never two adjacent blocks with the same symbol - it pessimistically assumes
--that may not be the case
--returns Nothing if the match fails, else the match
matchTape :: (Eq s) => [(Wild s, Count)] -> [(s, Count)] -> Maybe (TapeMatch s)
matchTape [] [] = Just $ Perfect
matchTape [] (t:ts) = Just $ TapeLeft (t :| ts)
matchTape (s:rest) []  = Just $ SkipLeft (s :| rest)
--else we can match the heads
matchTape (skipHead:restSkip) (tapeHead:restTape) = case matchTapeHeads skipHead tapeHead of
  --if the heads don't match, the whole match fails
  Nothing -> Nothing
  --if the heads perfectly square off, we can just recurse
  Just PerfectH -> matchTape restSkip restTape
  --else we have a leftover and match against it
  Just (SkipHLeft skip) -> matchTape (skip:restSkip) restTape
  Just (TapeHLeft tapeHead) -> matchTape restSkip (tapeHead:restTape)

--if you match two points, either they match perfectly, or some symbols of some count
--remain on one side
data PointMatch s = PerfectP | Lremains (s, Count) | Rremains (s, Count)

matchPoints :: (Eq s) => (Wild s, Count, Wild Dir) -> (s, Count, Dir) -> Maybe (PointMatch s)
matchPoints (ws, skipC, wd) (s, pointC, d) | (ws `matchEq` NotWild s) && (wd `matchEq` NotWild d)
  = matchCount skipC pointC >>= \case --passing through the maybe
      PerfectCount -> Just PerfectP
      --here we do make advantage of the ExpTape's invariant - if the skip isn't fully matched, nothing
      --on either side of it will help us
      FirstRemain _ -> Nothing
      --if some of the tape's point is not matched, then it remains on the tape
      --if we start matching from the right, the unmatched point is on the left
      SecondRemain remainC -> case mirrorDir d of
        L -> Just $ Lremains (s, remainC)
        R -> Just $ Rremains (s, remainC)
matchPoints _ _ = Nothing

-- generalizePoint :: (s, Int, Dir) -> (s, Count, Dir)
-- generalizePoint (s, i, d) = (s, Specific i, d)

--returns nothing if the skip is inapplicable, else returns a new tape
--the fact that the type is bit is only used when running off the tape, but for now I don't want to
--generalize that out (also ExpTape would have to be generalized)
applySkip :: Skip Bit -> (Phase, ExpTape Bit Count) -> Maybe (Phase, ExpTape Bit Count)
applySkip (Skip s e) (p, ExpTape leftTape tapePoint rightTape) | s ^. cstate == p
  = matchPoints (s^.point) tapePoint >>= \case
      --if we don't match the whole point, we can't care about the stuff on the other side
      --of the point
      Lremains remainP -> if (s^.ls) /= [] then Nothing else matchTape (s^.rs) rightTape >>= \case
        Perfect -> Just $ (e^.cstate, ExpTape undefined undefined undefined)

      Rremains remainP -> undefined
      PerfectP -> undefined
--if the phases don't match, we fail right away
applySkip _ _ = Nothing

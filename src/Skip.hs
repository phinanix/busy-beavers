module Skip where

import Relude hiding (mapMaybe)
import Control.Lens
import Data.Witherable

import Turing
import Count
import Util
import ExpTape

data Config s = Config
  { _cstate :: Phase
  , _ls :: [(VarOr s, Count)]
  , _c_point :: (VarOr s, Location Count)
  , _rs :: [(VarOr s, Count)]
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (Config s)

data Skip s = Skip
  { _start :: Config s
  , _end :: Config s
  , _hops :: Count --number of atomic TM steps
  , _halts :: Bool --true if the skip results in the machine halting
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (Skip s)

$(makeLenses ''Config)
$(makeLenses ''Skip)

--a Perfect match had no leftovers
--or we might have used up all of the skip and had some tape leftover, or vv
data HeadMatch s = PerfectH | TapeHLeft (s, InfCount) deriving (Eq, Ord, Show)

--we take the start of a skip and the start of a tape, match the symbols, match the counts
-- and return what's left of the tape if any
matchTapeHeads :: (Eq s) => (VarOr s, Count) -> (s, InfCount) -> EquationState s (HeadMatch s)
matchTapeHeads (varSB, skipC) (tb, tapeC) = do
  matchTapeVar varSB tb
  matchInfCount skipC tapeC >>= \case
    Empty -> pure PerfectH
    newCount -> pure (TapeHLeft (tb, newCount))

--when you match a skip and a tape, either they perfectly annihilate, the tape
--has at least one thing left, or the skip matches the whole tape and has at least
--one thing left
data TapeMatch s = Perfect
                 | TapeLeft (NonEmpty (s, InfCount))
                 | SkipLeft (NonEmpty (VarOr s, Count)) deriving (Eq, Ord, Show)
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
matchTape :: (Eq s) => [(VarOr s, Count)] -> [(s, InfCount)] -> EquationState s (TapeMatch s)
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

data TapeOrInf s = Infinite | NewTape [(s, InfCount)] deriving (Eq, Ord, Show, Generic)

--specializes matchTape to Bit, allowing the routine to
--signal the skip will match an infinite amount of tape
--fails if there is skip left-over
--first line is some seriously ugly munging but I'm not sure off the top of my head how to do better
--the function's type is (a -> Maybe b) -> Maybe (a,c) -> Maybe (b,c)
matchBitTape :: [(VarOr Bit, Count)] -> [(Bit, InfCount)] -> EquationState Bit (TapeOrInf Bit)
matchBitTape skip tape = bind matchToTapeOrInf $ matchTape skip tape where
  matchToTapeOrInf :: TapeMatch Bit -> EquationState Bit (TapeOrInf Bit)
  matchToTapeOrInf = \case
    Perfect -> pure $ NewTape []
    TapeLeft (toList -> newTape) -> pure $ NewTape newTape
    --if there's a count without any foralls, like a+3 where a is free, then
    --there is a chance to match the zeros at the end of the tape
    SkipLeft ((varOrBit, Count _ _ Empty) :| [])
      -> matchTapeVar varOrBit False $> NewTape []
    -- _notEmpty thereby must have foralls, and thus if the var matches zero,
    -- the skip matches the whole infinite rest of the tape
    SkipLeft ((varOrBit, _notEmpty) :| [])
      -> matchTapeVar varOrBit False $> Infinite
    SkipLeft _ -> nothingES

--if you match two points, either they match perfectly, or some symbols of some count
--remain on one side
data PointMatch s = PerfectP | Lremains (s, InfCount) | Rremains (s, InfCount) deriving (Eq, Ord, Show, Generic)

matchPoints :: (Eq s) => (VarOr s, Location Count) -> (s, Location InfCount) -> EquationState s (PointMatch s)
--if there is one of each symbol then they just match
matchPoints (skipS, One) (tapeS, One) = matchTapeVar skipS tapeS $> PerfectP
--if there is a single symbol in the skip, then the skip applies regardless of the tapeD
--and the rest of the matching is the same
matchPoints (skipS, One) (tapeS, Side tapeC tapeD) = matchTapeVar skipS tapeS
  >> matchInfsAndReturn (finiteCount 1) tapeS tapeC tapeD
matchPoints (_skipS, Side skipC _skipD) (_tapeS, One) = if skipC == finiteCount 1
  then error "Side may not contain a count of exactly 1"
  else nothingES
matchPoints (skipS, Side skipC skipD) (tapeS, Side tapeC tapeD)
  | skipD == tapeD = do
      matchTapeVar skipS tapeS
      matchInfsAndReturn skipC tapeS tapeC tapeD
matchPoints _ _ = nothingES
--strictly a helper function for the above
matchInfsAndReturn :: (Eq s) => Count -> s -> InfCount -> Dir -> EquationState s (PointMatch s)
matchInfsAndReturn skipC tapeS tapeC tapeD = matchInfCount skipC tapeC >>= \case
      Empty -> pure PerfectP
      --if some of the tape's point is not matched, then it remains on the tape
      --if we start matching from the right, the unmatched point is on the left
      remainC -> case mirrorDir tapeD of
        L -> pure $ Lremains (tapeS, remainC)
        R -> pure $ Rremains (tapeS, remainC)

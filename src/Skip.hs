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

dispVarOrAndCount :: (VarOr Bit, Count) -> Text
dispVarOrAndCount (vb, count) = "(" <> dispVarOrBit vb <> ", " <> dispCount count <> ") "

dispVarOrAndLocCount :: (VarOr Bit, Location Count) -> Text
dispVarOrAndLocCount (vb, Side count L) = "|>" <> dispVarOrAndCount (vb, count)
dispVarOrAndLocCount (vb, Side count R) = dispVarOrAndCount (vb, count) <> "<|"
dispVarOrAndLocCount (vb, One) = dispVarOrAndCount (vb, finiteCount 1) <> "<|"

dispConfig :: Config Bit -> Text
dispConfig (Config p ls point rs) = "phase: " <> dispPhase p <> "  "
  <> (mconcat $ dispVarOrAndCount <$> reverse ls)
  <> dispVarOrAndLocCount point
  <> (mconcat $ dispVarOrAndCount <$> rs)

dispSkip :: Skip Bit -> Text
dispSkip (Skip s e c halts) = "in " <> dispCount c <> " steps we turn\n"
  <> dispConfig s <> "\ninto: \n" <> dispConfig e <> (if halts then "\n and halt" else "")

--a Perfect match had no leftovers
--or we might have used up all of the skip and had some tape leftover
data HeadMatch s c = PerfectH | TapeHLeft (s, c) deriving (Eq, Ord, Show)

--we take the start of a skip and the start of a tape, match the symbols, match the counts
-- and return what's left of the tape if any
matchTapeHeads :: (Eq s) => (VarOr s, Count) -> (s, InfCount) -> Equations s (HeadMatch s InfCount)
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
matchTape :: (Eq s) => [(VarOr s, Count)] -> [(s, InfCount)] -> Equations s (TapeMatch s)
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

getTapeRemain :: TapeMatch s -> Maybe [(s, InfCount)]
getTapeRemain Perfect = Just Empty
getTapeRemain (TapeLeft ne) = Just $ toList ne
getTapeRemain (SkipLeft _) = Nothing

--data TapeOrInf s = Infinite | NewTape [(s, InfCount)] deriving (Eq, Ord, Show, Generic)

--specializes matchTape to Bit, allowing the routine to
--signal the skip will match an infinite amount of tape
--fails if there is skip left-over
-- matchBitTape :: [(VarOr Bit, Count)] -> [(Bit, InfCount)] -> Equations Bit (TapeOrInf Bit)
-- matchBitTape skip tape = bind matchToTapeOrInf $ matchTape skip tape where
--   matchToTapeOrInf :: TapeMatch Bit -> Equations Bit (TapeOrInf Bit)
--   matchToTapeOrInf = \case
--     Perfect -> pure $ NewTape []
--     TapeLeft (toList -> newTape) -> pure $ NewTape newTape
--     --if there's a count without any foralls, like a+3 where a is free, then
--     --there is a chance to match the zeros at the end of the tape
--     SkipLeft ((varOrBit, Count _ _ Empty) :| [])
--       -> matchTapeVar varOrBit False $> NewTape []
--     -- _notEmpty thereby must have foralls, and thus if the var matches zero,
--     -- the skip matches the whole infinite rest of the tape
--     SkipLeft ((varOrBit, _notEmpty) :| [])
--       -> matchTapeVar varOrBit False $> Infinite
--     SkipLeft _ -> nothingES

--if you match two points, either they match perfectly, or some symbols of some count
--remain on one side
data PointMatch s = PerfectP | Lremains (s, InfCount) | Rremains (s, InfCount) deriving (Eq, Ord, Show, Generic)

matchPoints :: (Eq s) => (VarOr s, Location Count) -> (s, Location InfCount) -> Equations s (PointMatch s)
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
matchInfsAndReturn :: (Eq s) => Count -> s -> InfCount -> Dir -> Equations s (PointMatch s)
matchInfsAndReturn skipC tapeS tapeC tapeD = matchInfCount skipC tapeC >>= \case
      Empty -> pure PerfectP
      --if some of the tape's point is not matched, then it remains on the tape
      --if we start matching from the right, the unmatched point is on the left
      remainC -> case mirrorDir tapeD of
        L -> pure $ Lremains (tapeS, remainC)
        R -> pure $ Rremains (tapeS, remainC)

--match a config to a tape, and return the lists that remain on each side of the
--tape after matching
matchConfigTape :: (Eq s) => Config s -> ExpTape s InfCount
  -> Equations s ([(s, InfCount)], [(s, InfCount)])
matchConfigTape (Config _p lsC pointC rsC) (ExpTape lsT pointT rsT)
  = matchPoints pointC pointT >>= \case
    Lremains remainP -> matchSides (remainP : lsT) rsT
    Rremains remainP -> matchSides lsT (remainP : rsT)
    PerfectP -> matchSides lsT rsT
  where
  matchSides left right = bisequence (mapMaybe getTapeRemain $ matchTape lsC left
                                     , mapMaybe getTapeRemain $ matchTape rsC right)

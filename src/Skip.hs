module Skip where

import Relude hiding (mapMaybe)
import Control.Lens
import Witherable
import Data.Text.Prettyprint.Doc
import Prettyprinter 

import Turing
import Count
import Util
import ExpTape

--a configuration of the machine's state - it is in a given phase, with the point of the tape and the stuff to the 
--left and right looking as specified
data Config s = Config
  { _cstate :: Phase
  , _ls :: [(s, Count)]
  , _c_point :: s
  , _rs :: [(s, Count)]
  } deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s) => NFData (Config s)

--at the end of a skip, you might've fallen off the L of the given pile of bits, or you might be in the middle of some 
--known bits, which is a config
data SkipEnd s = EndSide Phase Dir [(s, Count)] | EndMiddle (Config s) 
  deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s) => NFData (SkipEnd s)

--Zero and OneDir as they say, BothDirs goes the first count steps left and the second count steps right 
data Displacement c = Zero | OneDir Dir c | BothDirs c c deriving (Eq, Ord, Show, Generic, Functor) 
instance (NFData c) => NFData (Displacement c)

dispToInt :: Displacement InfCount -> Int 
dispToInt = \case 
  Zero -> 0
  OneDir L (NotInfinity (FinCount n)) -> -1 * fromIntegral n
  OneDir R (NotInfinity (FinCount n)) -> fromIntegral n
  BothDirs (NotInfinity (FinCount n)) (NotInfinity (FinCount m)) -> fromIntegral m - fromIntegral n
  other -> error $ "couldn't convert " <> show other <> " to an int"

data Skip s = Skip
  { _start :: Config s
  , _end :: SkipEnd s
  , _hops :: Count --number of atomic TM steps
  , _halts :: Bool --true if the skip results in the machine halting
  , _displacement :: Displacement Count 
  } deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s) => NFData (Skip s)

$(makeLenses ''Config)
$(makeLenses ''Skip)

prettyText :: Text -> Doc ann 
prettyText = pretty 

instance Pretty s => Pretty (Config s) where
  pretty (Config p ls point rs) = pretty $ "phase: " <> dispPhase p <> "  "
    <> mconcat (dispBitCount <$> reverse ls)
    <> dispPoint point
    <> mconcat (dispBitCount <$> rs)

instance Pretty s => Pretty (SkipEnd s) where
  pretty (EndSide p L ls) =  pretty $ "phase: " <> dispPhase p <> "  <|" <> mconcat (dispBitCount <$> ls)
  pretty (EndSide p R ls) =  pretty $ "phase: " <> dispPhase p <> " " <> mconcat (dispBitCount <$> ls) <> "|>"
  pretty (EndMiddle c) = pretty c

instance Pretty s => Pretty (Skip s) where
  pretty (Skip s e c halts displace) = prettyText "in " <> pretty (dispCount c) <> prettyText " steps we turn\n"
    <> pretty s <> prettyText "\ninto: \n" <> pretty e <> prettyText (if halts then "\n and halt" else "") 
    <> prettyText "\n displacement of: " <> show displace

getSkipEndPhase :: SkipEnd s -> Phase
getSkipEndPhase (EndSide p _ _) = p
getSkipEndPhase (EndMiddle (Config p _ _ _)) = p

-- --TODO: this code is not pretty but it works
configToET :: Config s -> (Phase, ExpTape s Count)
configToET (Config p ls point rs) = (p, ExpTape ls point rs)

-- etToConfig :: (Phase, ExpTape s Count) -> Config s
-- etToConfig (p, ExpTape ls point rs) = Config p ls point rs 

-- glomPointConfig :: (Eq s) => Config s -> Config s
-- glomPointConfig = etToConfig . fmap glomPointRight . fmap glomPointLeft . configToET
--   configToET & fmap glomPointLeft & fmap glomPointRight & etToConfig

matchBits :: (Eq s) => s -> s -> Equations ()
matchBits b c = eitherES $ unless (b == c) (Left "matched incorrect bits")

--a Perfect match had no leftovers
--or we might have used up all of the skip and had some tape leftover
data HeadMatch s c = PerfectH | TapeHLeft (s, c) deriving (Eq, Ord, Show)

--we take the start of a skip and the start of a tape, match the symbols, match the counts
-- and return what's left of the tape if any
matchTapeHeads :: (Eq s) => (s, Count) -> (s, InfCount) -> Equations (HeadMatch s InfCount)
matchTapeHeads (sb, skipC) (tb, tapeC) = do
  matchBits sb tb
  matchInfCount skipC tapeC >>= \case
    Empty -> pure PerfectH
    newCount -> pure (TapeHLeft (tb, newCount))

--when you match a skip and a tape, either they perfectly annihilate, the tape
--has at least one thing left, or the skip matches the whole tape and has at least
--one thing left
data TapeMatch s = Perfect
                 | TapeLeft (NonEmpty (s, InfCount))
                 | SkipLeft (NonEmpty (s, Count)) deriving (Eq, Ord, Show)
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
matchTape :: (Eq s) => [(s, Count)] -> [(s, InfCount)] -> Equations (TapeMatch s)
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
-- data PointMatch s = PerfectP | Lremains (s, InfCount) | Rremains (s, InfCount) deriving (Eq, Ord, Show, Generic)

-- matchPoints :: (Eq s) => (s, Location Count) -> (s, Location InfCount) -> Equations s (PointMatch s)
-- --if there is one of each symbol then they just match
-- matchPoints (skipS, One) (tapeS, One) = matchBits skipS tapeS $> PerfectP
-- --if there is a single symbol in the skip, then the skip applies regardless of the tapeD
-- --and the rest of the matching is the same
-- matchPoints (skipS, One) (tapeS, Side tapeC tapeD) = matchBits skipS tapeS
--   >> matchInfsAndReturn (finiteCount 1) tapeS tapeC tapeD
-- matchPoints (_skipS, Side skipC _skipD) (_tapeS, One) = if skipC == finiteCount 1
--   then error "Side may not contain a count of exactly 1"
--   else nothingES
-- matchPoints (skipS, Side skipC skipD) (tapeS, Side tapeC tapeD)
--   | skipD == tapeD = do
--       matchBits skipS tapeS
--       matchInfsAndReturn skipC tapeS tapeC tapeD
-- matchPoints _ _ = nothingES
-- --strictly a helper function for the above
-- matchInfsAndReturn :: (Eq s) => Count -> s -> InfCount -> Dir -> Equations s (PointMatch s)
-- matchInfsAndReturn skipC tapeS tapeC tapeD = matchInfCount skipC tapeC >>= \case
--       Empty -> pure PerfectP
--       --if some of the tape's point is not matched, then it remains on the tape
--       --if we start matching from the right, the unmatched point is on the left
--       remainC -> case mirrorDir tapeD of
--         L -> pure $ Lremains (tapeS, remainC)
--         R -> pure $ Rremains (tapeS, remainC)

--match a config to a tape, and return the lists that remain on each side of the
--tape after matching
matchConfigTape :: (Eq s) => Config s -> ExpTape s InfCount
  -> Equations ([(s, InfCount)], [(s, InfCount)])
matchConfigTape (Config _p lsC pointC rsC) (ExpTape lsT pointT rsT)
  = do
    matchBits pointC pointT
    matchSides lsT rsT
  where
  matchSides left right = bisequence (mapMaybe getTapeRemain $ matchTape lsC left
                                     , mapMaybe getTapeRemain $ matchTape rsC right)

matchSkipTape :: (Eq s) => Skip s -> ExpTape s InfCount 
  -> Equations ([(s, InfCount)], [(s, InfCount)])
matchSkipTape (Skip config end _hops _halts _displacement) tape = do 
  out@(lRem, rRem) <- matchConfigTape config tape 
  case end of     
    EndMiddle _ -> pure out
    EndSide _ph L _xs -> case lRem of 
      [] -> nothingES "matched and fell off left side, but left side was end of tape"
      _x1 : _x2 -> pure out 
    EndSide _ph R _xs -> case rRem of 
      [] -> nothingES "matched and fell off right side, but right side was end of tape"
      _x1 : _x2 -> pure out
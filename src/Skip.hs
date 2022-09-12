{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module Skip where

import Relude hiding (mapMaybe)
import Control.Lens
import Witherable
import Prettyprinter
import Data.Bitraversable (Bitraversable)
import Data.Bifoldable (Bifoldable)
import qualified Data.List.NonEmpty as NE 
import qualified Data.Set as S 
import qualified Data.Map.Monoidal as MM 

import Turing 
import Count
import Util
import ExpTape
import HaltProof
import Tape
import Relude.Extra
import Control.Exception
import Safe.Partial (Partial)

--when the machine halts, there are two ends of the tape plus a thing we push in the middle
data FinalTape c s = FinalTape ([(s, c)], [(s, c)]) (TapePush c Bit)
  deriving (Eq, Ord, Show, Generic)
instance (NFData s, NFData c) => NFData (FinalTape c s) 

--TODO write a pretty version
dispFinalTape :: (Show s, Show c) => FinalTape c s -> Text 
dispFinalTape = show 

instance (Pretty s, Pretty c, Show s, Show c) => Pretty (FinalTape c s) where 
  pretty = pretty . dispFinalTape

instance Functor (FinalTape c) where 
  fmap f (FinalTape (ls,rs) tp) = FinalTape (first f <$> ls, first f <$> rs) tp 

instance Tapeable (FinalTape InfCount Bit) where 
  ones (FinalTape (ls,rs) tp) = countList ls + countList rs + ones tp 

--a configuration of the machine's state - it is in a given phase, with the point of the tape
--and the stuff to the left and right looking as specified
data Config c s = Config
  { _cstate :: Phase
  , _ls :: [(s, c)]
  , _c_point :: s
  , _rs :: [(s, c)]
  } deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s, NFData c) => NFData (Config c s)

instance Bifunctor Config where
    bimap f g (Config ph ls p rs) = Config ph (bimap g f <$> ls) (g p) (bimap g f <$> rs)

instance Bifoldable Config where
  bifoldMap = bifoldMapDefault

instance Bitraversable Config where
  bitraverse f g (Config ph ls p rs) = Config ph <$> (bitraverse g f <%> ls) <*> g p <*> (bitraverse g f <%> rs)


data TapePush c s = Side Dir [(s, c)] 
                  | Middle (ExpTape s c) 
                  deriving (Eq, Ord, Show, Generic) 
instance (NFData c, NFData s) => (NFData (TapePush c s))

instance Functor (TapePush c) where 
  fmap f = \case 
    Side dir xs -> Side dir $ first f <$> xs
    Middle et -> Middle $ first f et

instance Bifunctor TapePush where 
  bimap = bimapDefault 
instance Bifoldable TapePush where 
  bifoldMap = bifoldMapDefault

instance Bitraversable TapePush where 
  bitraverse f g = \case
    Side d xs -> Side d <$> bitraverse g f <%> xs
    Middle tape -> Middle <$> bitraverse g f tape

instance Tapeable (TapePush InfCount Bit) where 
  ones = \case 
    Side _dir xs -> countList xs 
    Middle et -> ones et 

--at the end of a skip, you might've fallen off the L of the given pile of bits, or you might be in the middle of some 
--known bits, which is a config
data SkipEnd c s = SkipStepped Phase (TapePush c s)
                 | SkipHalt (TapePush c Bit) --the machine halts and puts this out onto the tape
                 | SkipUnknownEdge Edge 
                 | SkipNonhaltProven (HaltProof s)  
  deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s, NFData c) => NFData (SkipEnd c s)

$(makePrisms ''SkipEnd)

instance Bifunctor SkipEnd where
  bimap = bimapDefault

instance Bifoldable SkipEnd where
  bifoldMap = bifoldMapDefault

instance Bitraversable SkipEnd where
  bitraverse f g = \case
    SkipStepped p tp -> SkipStepped p <$> bitraverse f g tp 
    SkipHalt tp -> SkipHalt <$> bitraverse f pure tp 
    SkipUnknownEdge e -> pure $ SkipUnknownEdge e
    SkipNonhaltProven hp -> SkipNonhaltProven <$> (g <%> hp)

data Skip c s = Skip
  { _start :: Config c s
  , _end :: SkipEnd c s
  , _hops :: c --number of atomic TM steps
  -- , _displacement :: Displacement c
  } deriving (Eq, Ord, Show, Generic, Functor)
instance (NFData s, NFData c) => NFData (Skip c s)

instance Bifunctor Skip where
  bimap f g (Skip c se hop) = Skip (bimap f g c) (bimap f g se) (f hop)

instance Bifoldable Skip where
  bifoldMap = bifoldMapDefault

instance Bitraversable Skip where
  bitraverse f g (Skip c se hop)
    = Skip <$> bitraverse f g c <*> bitraverse f g se <*> f hop

--(neg left, pos right, 0 current head pos)
--I think this means len_l is always <=0, len_r >=0
data ReadShift = ReadShift {_len_l :: Steps, _len_r :: Steps, _shift_dist :: Steps}
  deriving (Eq, Ord, Show, Generic)
instance NFData ReadShift 

instance Semigroup ReadShift where 
  (ReadShift l1 r1 s1) <> (ReadShift l2 r2 s2) 
    = ReadShift (min l1 l2') (max r1 r2') (s1 + s2)
   where
    l2' = l2 + s1 
    r2' = r2 + s1 

instance Monoid ReadShift where 
  mempty = ReadShift 0 0 0 

$(makeLenses ''Config)
$(makeLenses ''Skip)
$(makeLenses ''ReadShift)

instance Pretty s => Pretty (Config Count s) where
  pretty (Config p ls point rs) = pretty $ "phase: " <> dispPhase p <> "  "
    <> mconcat (dispETPair <$> reverse ls)
    <> dispPoint point
    <> mconcat (dispETPair <$> rs)

instance Pretty s => Pretty (TapePush Count s) where
  pretty (Side L ls) =  pretty $ "  <|" <> mconcat (dispETPair <$> ls)
  pretty (Side R ls) =  pretty $ " " <> mconcat (dispETPair <$> ls) <> "|>"
  pretty (Middle c) = pretty c

instance Pretty s => Pretty (SkipEnd Count s) where 
  pretty = \case 
    SkipStepped ph tp -> pretty $ "phase: " <> dispPhase ph <> showP tp 
    SkipHalt tp -> prettyText $ "halted, pushing: " <> showP tp 
    SkipUnknownEdge e -> prettyText $ "skip reaches unknown edge: " <> showP e
    SkipNonhaltProven hp -> prettyText $ "skip reaches known nonhalting: " <> showP hp 

instance Pretty s => Pretty (Skip Count s) where
  pretty (Skip s e c) = prettyText "in " <> pretty (dispCount c) <> prettyText " steps we turn\n"
    <> pretty s <> prettyText "\ninto: \n" <> pretty e <> "\n"

instance Pretty ReadShift where 
  pretty (ReadShift l r s) = prettyText $ "RS l " <> show l 
    <> " r " <> show r <> " s " <> show s 

getSkipEndPhase :: SkipEnd c s -> Maybe Phase
getSkipEndPhase = \case
  SkipStepped p _ -> Just p
  _ -> Nothing 

-- --TODO: this code is not pretty but it works
configToET :: Config c s -> (Phase, ExpTape s c)
configToET (Config p ls point rs) = (p, ExpTape ls point rs)

etToConfig :: Phase -> ExpTape s c -> Config c s
etToConfig p (ExpTape ls point rs) = Config p ls point rs

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
                 | SkipLeft (NonEmpty (s, Count)) 
                 deriving (Eq, Ord, Show)

tapeMatchToMaybeTapeLeft :: TapeMatch s -> Maybe [(s, InfCount)]
tapeMatchToMaybeTapeLeft = \case 
  Perfect -> Just [] 
  TapeLeft (x :| xs) -> Just (x : xs) 
  SkipLeft _ -> Nothing 

pattern ETapeLeft :: [(s, InfCount)] -> TapeMatch s
pattern ETapeLeft xs <- (tapeMatchToMaybeTapeLeft -> (Just xs)) where 
  ETapeLeft [] = Perfect 
  ETapeLeft (x : xs) = TapeLeft (x :| xs) 
{-# COMPLETE ETapeLeft, SkipLeft  #-}

tapeMatchToMaybeSkipLeft :: TapeMatch s -> Maybe [(s, Count)]
tapeMatchToMaybeSkipLeft = \case 
  Perfect -> Just []
  SkipLeft (x :| xs) -> Just (x : xs)
  TapeLeft _ -> Nothing
  
pattern ESkipLeft :: [(s, Count)] -> TapeMatch s 
pattern ESkipLeft xs <- (tapeMatchToMaybeSkipLeft -> (Just xs)) where 
  ESkipLeft [] = Perfect 
  ESkipLeft (x : xs) = SkipLeft (x :| xs) 
{-# COMPLETE ESkipLeft, TapeLeft  #-}

--note: this routine does not make advantage of the fact that the ExpTape has the invariant
--that there are never two adjacent blocks with the same symbol - it pessimistically assumes
--that may not be the case
--given a skip to match against a tape, returns the remaining tape that's left after consuming
--all the tape that matches the skip, the rest of the unmatched skip, or
--fails, returning nothing
--example :: matchTape [(F, 2), (T, 1)] [(F, 2), (T, 3), (F, x)] == [(T, 2), (F, x)]
--returns Nothing if the match fails, else the match
{-
so there's a problem, which is that when we get to the last thing in the skip, it may not match the last 
variable right. consider matchTape [(F, x) (T, 1), (F, x)] [(F, 2), (T, 1), (F, 3)] 
the answer should be (x -> 2) [(F, 1)], but instead I think we fail. 

The way we solve this, is we match two tapes all the way except for the last pair of each of the
two skip lists as normal. Then for the last pair on each side, we see if it is already mapped, and if it is, 
we see if that's compatible with the last matchup, and return the answer if so. If we have now resolved neither 
side and both sides contain exactly the same boundvar, then we map said boundvar to the intersection of the 
two relevant tapecounts (or fail if that is zero). Otherwise, we map each last bit which hasn't yet been resolved
to the maximal thing possible as normal. 
-}
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

matchTwoCounts :: Partial => (Count, Count) -> (InfCount, InfCount) -> Equations (InfCount, InfCount) 
matchTwoCounts (lC@(Count _n _as xs), rC@(Count _m _bs ys)) (lT, rT) 
  = case toList $ S.intersection (MM.keysSet xs) (MM.keysSet ys) of 
    Empty -> do 
      lRes <- matchInfCount lC lT
      rRes <- matchInfCount rC rT 
      pure (lRes, rRes)
    [cV] -> 
      -- case (lT, rT) of 
      -- (NotInfinity lTC, NotInfinity rTC) -> 
      do 
        (lVars, lTRem) <- removeCommonConstsInf lC lT
        (rVars, rTRem) <- removeCommonConstsInf rC rT
        --TODO: for now we only handle the case where lVars and rVars are exactly 1 var each, 
        --we'll handle other stuff later 
        case (MM.assocs lVars, MM.assocs rVars) of 
          ([], _) -> error "unreachable mTC1"
          (_, []) -> error "unreachable mTC2"
          {- Example: 10x into 37 and 11x into 54 gives 
          10*3 + 7 and 11*4 + 10 and we want to send x to the smaller of 3 and 4 
          giving x->3 and left: 37 - (10*3) right: 54 - (11*3)
          -}
          ([(lV, Sum lCoeff)], [(rV, Sum rCoeff)]) -> assert (lV == rV && rV == cV) $ let 
            (lQ, _lRem) = divRemInfCount lTRem lCoeff 
            (rQ, _rRem) = divRemInfCount rTRem rCoeff 
            (likes, _, _) = likeTermsInf lQ rQ
            in addEquation (cV, likes) $ 
              pure (lTRem `unsafeSubInfCountFromInfCount` (lCoeff `nTimes` likes), 
                     rTRem `unsafeSubInfCountFromInfCount` (rCoeff `nTimes` likes))
          (_lVs, _rVs) -> error $ "there was more than one variable in matchTwoCounts: " 
            <> showP lC <> " " <> showP rC
    _cVs -> error $ "there was more than one common variable in matchTwoCounts: " 
            <> showP lC <> " " <> showP rC

-- try common variables, then if there aren't do the regular thing
-- then if there are, first reduce common parts (non var parts), 
-- then do the like, map to the intersection of the rhs thing

matchTwoTapes :: forall s. (Eq s) => ([(s, Count)], [(s, InfCount)]) -> ([(s, Count)], [(s, InfCount)])
  -> Equations (TapeMatch s, TapeMatch s)
matchTwoTapes (lsS, lsT) (rsS, rsT) = case (unsnoc lsS, unsnoc rsS) of 
  (Nothing, Nothing) -> pure (ETapeLeft lsT, ETapeLeft rsT) 
  (Nothing, Just (rSstart, rSlast)) -> do 
    let lRes = ETapeLeft lsT
    rRes <- answerOneSide rSstart rSlast rsT 
    pure (lRes, rRes)
  (Just (lSstart, lSlast), Nothing) -> do 
    let rRes = ETapeLeft rsT 
    lRes <- answerOneSide lSstart lSlast lsT 
    pure (lRes, rRes)
  (Just (lSstart, (lSlastS, lSlastC)), Just (rSstart, (rSlastS, rSlastC))) 
    -> case bisequence (matchTape lSstart lsT, matchTape rSstart rsT) of 
    Equations (Left msg) -> Equations (Left msg)
    Equations (Right (map, (ESkipLeft skipLs, ESkipLeft skipRs))) -> 
      Equations $ Right (map, (ESkipLeft (skipLs ++ [(lSlastS, lSlastC)]), 
                              ESkipLeft (skipRs ++ [(rSlastS, rSlastC)])))
    Equations (Right (map, (ESkipLeft skipLs, TapeLeft (rTapeHead :| rTapeRest)))) -> do 
      let lRes = ESkipLeft $ skipLs ++ [(lSlastS, lSlastC)]
      rRes <- lastVarOneSide map (rSlastS, rSlastC) rTapeHead rTapeRest
      pure (lRes, rRes)
    Equations (Right (map, (TapeLeft (lTapeHead :| lTapeRest), ESkipLeft skipRs))) -> do 
      lRes <- lastVarOneSide map (lSlastS, lSlastC) lTapeHead lTapeRest 
      let rRes = ESkipLeft $ skipRs ++ [(rSlastS, rSlastC)]
      pure (lRes, rRes)
    Equations (Right (map, (TapeLeft ((lTS, lTC) :| lTapeRest), TapeLeft ((rTS, rTC) :| rTapeRest)))) -> let
      (lSCBound, rSCBound) = bimapBoth (partiallyUpdateCount map) (lSlastC, rSlastC)
      secondEqns = do 
        matchBits lSlastS lTS 
        matchBits rSlastS rTS 
        (lCrem, rCrem) <- matchTwoCounts (lSCBound, rSCBound) (lTC, rTC) 
        pure (ETapeLeft $ delHeadZero $ (lTS, lCrem) :| lTapeRest, 
              ETapeLeft $ delHeadZero $ (rTS, rCrem) :| rTapeRest)
      in case secondEqns of 
        Equations (Left msg) -> Equations $ Left $ msg <> "\nalso some boundVar shenanigans happened"
        Equations (Right (subMap, ans)) -> case mergeEqns map subMap of 
          Left msg -> error $ "merge failed, but I think it shouldn't ever fail: " <> msg 
          Right newMap -> Equations $ Right (newMap, ans) 
  where 
    delHeadZero ((s, c) :| rest) = case c of 
      Empty -> rest 
      ne -> (s, ne) : rest 
    answerOneSide :: [(s, Count)] -> (s, Count) -> [(s, InfCount)] -> Equations (TapeMatch s)
    answerOneSide skipStart skipLast tapeHalf = case matchTape skipStart tapeHalf of 
     Equations (Left msg) -> Equations $ Left msg 
     Equations (Right (map, SkipLeft skipLeft)) -> 
       Equations (Right (map, SkipLeft (skipLeft <> (skipLast :| []))))
     Equations (Right (map, Perfect)) ->
       Equations (Right (map, SkipLeft $ skipLast :| [] ))
     Equations (Right (map, TapeLeft (rTapeHead :| rTapeRest))) -> 
      lastVarOneSide map skipLast rTapeHead rTapeRest 
    lastVarOneSide :: Map BoundVar InfCount -> (s, Count) -> (s, InfCount) -> [(s, InfCount)]
      -> Equations (TapeMatch s) 
    lastVarOneSide map skipLast rTapeHead rTapeRest =       
      {-
      what we do here is 
        1) send any boundVars in rSlast to what they are bound to, using map
        2) match rSlast and rTapeHead
        3) case on the result and pack up the answer
      -}
      let rSlastBound = second (partiallyUpdateCount map) skipLast  
      in case matchTapeHeads rSlastBound rTapeHead of 
          Equations (Left msg) -> Equations $ Left $ msg <> "\nalso some boundVar shenanigans happened"
          Equations (Right (subMap, PerfectH)) -> case mergeEqns map subMap of 
            Left msg -> error $ "merge failed, but I think it shouldn't ever fail: " <> msg 
            Right newMap -> Equations $ Right (newMap, ETapeLeft rTapeRest)
          Equations (Right (subMap, TapeHLeft thl)) -> case mergeEqns map subMap of 
            Left msg -> error $ "merge failed, but I think it shouldn't ever fail: " <> msg 
            Right newMap -> Equations $ Right (newMap, TapeLeft (thl :| rTapeRest))


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
matchConfigTape :: (Eq s, Show s, Pretty s) => Config Count s -> ExpTape s InfCount
  -> Equations ([(s, InfCount)], [(s, InfCount)])
matchConfigTape (Config _p lsC pointC rsC) (ExpTape lsT pointT rsT)
  = do
    matchBits pointC pointT
    mapMaybe (bitraverseBoth getTapeRemain) $ matchTwoTapes (lsC, lsT) (rsC, rsT) 
  -- where
  -- matchSides left right = trace ("lst rst" <> showP lsT <> " " <> showP rsT) $ let 
  --   leftAns = mapMaybe getTapeRemain $ matchTape lsC left
  --   rightAns = mapMaybe getTapeRemain $ matchTape rsC right
  --   in trace ("leftAns " <> showP (getEquations leftAns) <> " rightAns " <> showP (getEquations rightAns)) 
  --     bisequence (leftAns, rightAns)


matchSkipTape :: (Eq s, Show s, Pretty s) => Skip Count s -> ExpTape s InfCount
  -> Equations ([(s, InfCount)], [(s, InfCount)])
matchSkipTape (Skip config end _hops) tape = do
  out@(lRem, rRem) <- matchConfigTape config tape
  
  let checkTP :: forall g. (TapePush Count g -> Equations ()) = \case 
        (Side L _xs) -> case lRem of
          [] -> nothingES "matched and fell off left side, but left side was end of tape"
          _x1 : _x2 -> pure ()
        (Side R _xs) -> case rRem of
          [] -> nothingES "matched and fell off right side, but right side was end of tape"
          _x1 : _x2 -> pure ()
        _ -> pure ()

  case end of     
    SkipStepped _ph tp -> do 
      checkTP tp 
      pure () 
    SkipHalt tp -> do 
      checkTP tp 
      pure ()
    SkipUnknownEdge _e -> pure ()
    SkipNonhaltProven _hp -> pure ()
  
  pure out 



isSameInAsOut :: forall c s. (Monoid c, Eq c) => Skip c s -> Bool
isSameInAsOut (Skip start end _) = addUp start == addUp end
  where
    addUp :: (Bifoldable b) => b c s -> c
    addUp = bifoldMap id (const mempty)

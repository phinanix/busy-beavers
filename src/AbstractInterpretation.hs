module AbstractInterpretation where


import Relude
import Control.Lens
import qualified Relude.Unsafe as U
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import qualified Data.List.NonEmpty as NE
import Relude.Extra (bimapBoth)
import Prettyprinter
import Safe.Exact
import Control.Exception (assert)
import Safe.Partial


import Util
import Count
import Skip
import ExpTape
import Turing
import TapeSymbol
import HaltProof
import SimulateSkip
import Graphs

data AbsAny s = Base !s | MultipleAny deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (AbsAny s)

dispAbsAny :: (Pretty s) => AbsAny s -> Text
dispAbsAny = \case
    Base s -> showP s
    MultipleAny -> ".*"

instance Pretty s => Pretty (AbsAny s) where
    pretty = prettyText . dispAbsAny

instance (TapeSymbol s) => TapeSymbol (AbsAny s) where
  blank = Base blank
  allSymbols = Base <$> allSymbols
  getPoint = \case
    Base s -> getPoint s
    MultipleAny -> error "getpoint multiple any"
  toBits = \case
    Base s -> toBits s
    MultipleAny -> error "toBits multipleany"
  fromBits = first (fmap Base) . fromBits
  initBook = mapBook Base . initBook

{-
algorithm: keep track of k bits near the machine's head, other bits could be anything. if 
you loop in that representation, then you run forever. 
bits of the algorithm: 
 - we need a data structure that represents the partial tape 
 - we need a starting config 
 - advance a given config forward using a machine's book 
 - if the advance doesn't work, then we need to shift the bit of the tape which is 
   represented so that there is tape for the machine to grab

parameters: 
 - which k do we try and do we try more if it fails
 - how many nodes do we search

the size of the tree in k is num_states * 2^(k+1)
at 1000 nodes, we can exhaustively search k=6
but up to k = 10 seems plausibly useful, unclear, since when proofs exist they are
unlikely to use the whole tree. k=10 gives 5*2^11 = 10240
-}

forwardNearHeadInterp :: forall s. (TapeSymbol s) => Int -> Int -> Turing -> Maybe (HaltProof s)
forwardNearHeadInterp startK endK m 
  = rightToMaybe $ foldl' loopFunc (Left True) [startK, startK + 2.. endK] 
  --asum $ doDFS <$> [startK, startK+2.. endK]
  where
    {-we need a sum of 3 things: 
  1) hit nodelimit, give up
  2) halted, try with more tape
  3) found proof, return proof
  Either Bool (HaltProof s) works, where the bool is True if we should continue
  -}
    loopFunc eitherProof nextK = case eitherProof of 
      Right pf -> Right pf 
      Left False -> Left False 
      Left True -> case doDFS nextK of 
        Right (NoSuccess numNodes) -> Right $ NearHeadAI nextK numNodes 
        Left _msg -> Left False
        Right (Success _p) -> Left True 
    doDFS k = dfs 1000 1000 (nearHeadGetNextConfigs k m skips) 
      successCond (Just $ nearHeadInitialConfig k)
    skips = mapBook Base $ initBook @s m
    --we found what we were looking for if we find Nothing, since that means
    --either the machine halts or we hit an unknown edge
    --and we need to abort the search 
    successCond :: Maybe (Phase, ExpTape (AbsAny s) InfCount) -> Bool
    successCond = (== Nothing)
nearHeadInitialConfig :: (TapeSymbol s) => Int -> (Phase, ExpTape (AbsAny s) InfCount)
nearHeadInitialConfig k = (Phase 0, ExpTape 
  [(blank, NotInfinity $ FinCount $ fromIntegral $ k `div` 2), 
    (MultipleAny, NotInfinity One)]
  blank 
  [(blank, NotInfinity $ FinCount $ fromIntegral $ k `div` 2 + k `mod` 2), 
    (MultipleAny, NotInfinity One)])


--the nothing is in case we fail due to an unknown edge or halting 
nearHeadGetNextConfigs :: forall s. (TapeSymbol s) 
  => Int -> Turing -> SkipBook (AbsAny s) -> Maybe (Phase, ExpTape (AbsAny s) InfCount) 
  -> [Maybe (Phase, ExpTape (AbsAny s) InfCount)]
nearHeadGetNextConfigs _ _ _  Nothing = error "next config nothing?"
nearHeadGetNextConfigs k m skips (Just (ph, tape)) = case skipStep m skips ph tape of
  Unknown _e -> [Nothing]
  Stopped {} -> [Nothing]
  Stepped _ newPh (ExpTape _ MultipleAny _) _ _ _ -> trace ("newph " <> show newPh) branchAndContinue
  Stepped _ newPh newTape _ _ _ -> [Just (newPh, newTape)]
  NonhaltProven _hp -> []
  MachineStuck -> branchAndContinue
  where
  branchAndContinue = do
    newTape <- branchTape tape
    cleanTape <$$$> nearHeadGetNextConfigs k m skips (Just (ph, newTape))
  branchTape :: ExpTape (AbsAny s) InfCount -> [ExpTape (AbsAny s) InfCount]
  branchTape tape@(ExpTape ls p rs) = case ls of
      [] -> error "exptape ls empty in branchTape"
      ((MultipleAny, _c) : _rest) -> allSymbols >>= (\s -> pure $
          ExpTape ((s, NotInfinity One) : ls) p rs)
      _other -> case rs of
          [] -> error "exptape rs empty in branchTape"
          ((MultipleAny, _c) : _rest) -> allSymbols >>= (\s -> pure $
              ExpTape ls p ((s, NotInfinity One) : rs))
          _other -> error $ "nothing to branch on:" <> showP tape
  cleanTape :: ExpTape (AbsAny s) InfCount -> ExpTape (AbsAny s) InfCount
  cleanTape tape@(ExpTape ls p rs) = case (getLiveRegion ls, getLiveRegion rs) of
      ((lsInit, lsTail), (rsInit, rsTail)) -> if length (lsInit <> rsInit) <= k then tape else
        case (lsInit, lsTail) of
        (l : lsRest, moreLs@((MultipleAny, _c) : _))
          -> cleanTape $ ExpTape ((first Base <$> init (l :| lsRest)) <> moreLs) p rs
        _other -> case (rsInit, rsTail) of
          (r : rsRest, moreRs@((MultipleAny, _c) : _))
            -> cleanTape $ ExpTape ls p ((first Base <$> init (r :| rsRest)) <> moreRs)
          _other -> error $ "no ability to clean tape: " <> showP tape

  getLiveRegion :: [(AbsAny s, InfCount)] -> ([(s, InfCount)], [(AbsAny s, InfCount)])
  getLiveRegion = first (fmap (first notMult)) . break (\case
                      (MultipleAny, _) -> True
                      _ -> False)
  notMult = \case
    MultipleAny -> error "was mult when notmult"
    (Base s) -> s
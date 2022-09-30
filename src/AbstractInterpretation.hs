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
-}

forwardNearHeadInterp :: forall s. (TapeSymbol s) => Int -> Turing -> Maybe (HaltProof s)
forwardNearHeadInterp k m = case dfs 1000 1000 getNextConfigs successCond (Just initialConfig) of 
  Right NoSuccess -> u
  Left msg -> u 
  Right (Success _p) -> u 
  where
    skips = mapBook Base $ initBook @s m
    successCond :: Maybe (Phase, ExpTape (AbsAny s) InfCount) 
    successCond = u
    initalConfig :: (Phase, ExpTape (AbsAny s) InfCount)
    initalConfig = (Phase 0, ExpTape [(MultipleAny, NotInfinity One)]
                               blank [(MultipleAny, NotInfinity One)])
    --the nothing is in case we fail due to an unknown edge or halting 
    getNextConfigs :: Maybe (Phase, ExpTape (AbsAny s) InfCount) -> [Maybe (Phase, ExpTape (AbsAny s) InfCount)]
    getNextConfigs (Just (ph, tape)) = case skipStep m skips ph tape of
      Unknown x0 -> [Nothing]
      Stopped ic ft sk -> [Nothing]
      Stepped _ newPh newTape _ _ _ -> [Just (newPh, newTape)]
      NonhaltProven hp -> []
      MachineStuck -> do
        newTape <- branchTape tape
        cleanTape <$$$> getNextConfigs (Just (ph, newTape))
    getNextConfigs Nothing = error "next config nothing?"
    branchTape :: ExpTape (AbsAny s) InfCount -> [ExpTape (AbsAny s) InfCount]
    branchTape tape@(ExpTape ls p rs) = case ls of
        [] -> error "exptape ls empty in branchTape"
        ((MultipleAny, _c) : _rest) -> allSymbols >>= (\s -> pure $
            ExpTape ((s, NotInfinity One) : ls) p rs)
        other -> case rs of
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
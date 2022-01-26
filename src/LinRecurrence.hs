module LinRecurrence where 


import Relude
import Control.Lens
import Data.Map.Monoidal (assocs, keysSet)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter
import Data.Either.Combinators

import Data.Bits (Bits(bit))
import Data.List (minimumBy, findIndex)
import qualified Data.List.NonEmpty as NE
import Relude.Extra (bimapBoth)
import Relude.Foldable (Bitraversable)
import qualified Relude.Unsafe as Unsafe
import Safe.Exact
import Control.Exception (assert)
import Data.Foldable
import Relude.Unsafe ((!!))
import qualified Relude.Unsafe as U
import Data.Bifoldable (Bifoldable)
import Graphs
import Data.Bitraversable

import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
import SimulationLoops
import Display
import Safe.Partial
import HaltProof
import Glue


--given a list, sorts it and uses this to find whether it contains a duplicate
hasPair :: (Ord a) => [a] -> Maybe (Int, Int)
hasPair [] = Nothing
hasPair xs = let 
    enumXs = zip [0,1..] xs 
    sortedXs = sortOn snd enumXs 
    xsPairs = zip (U.init sortedXs) (U.tail sortedXs)
    in 
    --find the first element of the list where the two things are equal
    --then return their indices
    (\((i, _a), (j, _b)) -> (i,j)) <$> 
      find (\((_i, a), (_j, b)) -> a==b) xsPairs


--works by sorting the history, determining if there is a duplicate, 
--and if so, there is a cycle and we can return a haltproof right away
histHasDuplicate :: (Ord s, Ord c) => ReverseTapeHist s c -> Maybe HaltProof 
histHasDuplicate (ReverseTapeHist revHist) = mkHP <$> hasPair (reverse revHist) 
  where
    mkHP (i, j) = Cycle i j

--detects lin recurrence, as determined by the history
--currently disphist is implemented in a bad way (skips can care about a whole chunk of symbols) so 
--this function isn't actually writeable, so I should fix that first 
detectLinRecurrence :: TapeHist Bit InfCount 
  -> DispHist 
  -> Maybe HaltProof
detectLinRecurrence hist disphist = undefined 
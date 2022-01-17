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
import Data.Bifoldable (Bifoldable)
import Graphs
import Data.Bitraversable

--works by sorting the history, determining if there is a duplicate, and if so, there is a cycle and 
--we can return a haltproof right away
histHasDuplicate :: (Ord s, Ord c) => ReverseTapeHist s c -> Maybe HaltProof 
histHasDuplicate (ReverseTapeHist histList) = let 
    histLen = length histList
    enumHist = zip [(histLen - 1), (histLen -2)..] histList
    sortedHist = sortOn snd enumHist
    in 
    undefined

--detects lin recurrence, as determined by the history
--currently disphist is implemented in a bad way (skips can care about a whole chunk of symbols) so 
--this function isn't actually writeable, so I should fix that first 
detectLinRecurrence :: ReverseTapeHist Bit InfCount -> ReverseDispHist -> Maybe HaltProof
detectLinRecurrence hist disphist = undefined 
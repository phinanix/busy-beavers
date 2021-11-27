module BackwardSearch where 

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter
import Data.Either.Combinators
import Safe.Exact

import Graphs
import Turing 
import Skip 

newtype BWNode = BWNode (Turing, Config Natural Bit) deriving (Eq, Ord, Show, Generic)

instance Graph BWNode where 
  getAdjacent (BWNode (machine, config)) = []
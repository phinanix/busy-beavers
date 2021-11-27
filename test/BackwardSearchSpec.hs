module BackwardSearchSpec where 

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter
import Data.Either.Combinators
import Safe.Exact

import Test.Hspec
import Test.QuickCheck hiding (Success)

spec :: Spec
spec = do 
    pure ()
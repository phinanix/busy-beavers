module GraphsSpec where 

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

import Graphs 

-- first int is how many children you have, second one is just a tag
newtype GraphWithBranches = GraphWithBranches (Int, Int) deriving (Eq, Ord, Show, Generic)

getAdjacentGWB (GraphWithBranches (n, _tag)) = GraphWithBranches . (n - 1,) <$> take n [0, 1 ..] 

newtype BinarySeq = BinarySeq [Bool] deriving (Eq, Ord, Show, Generic)

getAdjacentBS (BinarySeq xs) = (\x -> BinarySeq (x : xs)) <$> [False, True]

spec :: Spec
spec = do 
  describe "dfs" $ do 
    it "exhausts a simple graph" $
      dfs 5 100 getAdjacentGWB (const False) (GraphWithBranches (4,0)) `shouldBe` (Right NoSuccess)
    it "finds a node" $ 
      dfs 5 100 getAdjacentGWB (== GraphWithBranches (0,0)) (GraphWithBranches (5,0)) `shouldBe` (Right $ Success $ GraphWithBranches . (,0) <$> [5,4..0])
    it "bottoms out if the search isn't deep enough" $
      dfs 4 100 getAdjacentGWB (== GraphWithBranches (0,0)) (GraphWithBranches (5,0)) `shouldSatisfy` (has _Left)
    it "finds a node with a lot of branching paths" $ 
      dfs 7 500 getAdjacentBS (== BinarySeq (take 6 (repeat True))) (BinarySeq []) `shouldBe` 
        (Right $ Success $ (\n -> BinarySeq (take n (repeat True))) <$> [0.. 6])
    it "fails if there are too many nodes" $
      dfs 10 100 getAdjacentBS (== BinarySeq (take 7 (repeat True))) (BinarySeq []) `shouldSatisfy` (has _Left)
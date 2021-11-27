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

instance Graph GraphWithBranches where  
    getAdjacent (GraphWithBranches (n, _tag)) = GraphWithBranches . (n - 1,) <$> take n [0, 1 ..] 

newtype BinarySeq = BinarySeq [Bool] deriving (Eq, Ord, Show, Generic)
instance Graph BinarySeq where 
    getAdjacent (BinarySeq xs) = (\x -> BinarySeq (x : xs)) <$> [False, True]

spec :: Spec
spec = do 
  describe "dfs" $ do 
    it "exhausts a simple graph" $
      dfs 5 100 (const False) (GraphWithBranches (4,0)) `shouldBe` (Just NoSuccess)
    it "finds a node" $ 
      dfs 5 100 (== GraphWithBranches (0,0)) (GraphWithBranches (5,0)) `shouldBe` (Just $ Success $ GraphWithBranches . (,0) <$> [5,4..0])
    it "bottoms out if the search isn't deep enough" $
      dfs 4 100 (== GraphWithBranches (0,0)) (GraphWithBranches (5,0)) `shouldBe` Nothing
    it "finds a node with a lot of branching paths" $ 
      dfs 7 500 (== BinarySeq (take 6 (repeat True))) (BinarySeq []) `shouldBe` 
        (Just $ Success $ (\n -> BinarySeq (take n (repeat True))) <$> [0.. 6])
    it "fails if there are too many nodes" $
      dfs 10 100 (== BinarySeq (take 7 (repeat True))) (BinarySeq []) `shouldBe`Nothing
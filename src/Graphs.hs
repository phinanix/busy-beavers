module Graphs where 

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter
import Data.Either.Combinators
import Safe.Exact
import Util


--NoSuccess means we explored the whole graph and proved there are no success nodes in it
--Success v means we found one success, and gives the list of vertices from the start of the 
--search that takes you to the successful node 
data SearchResult v = NoSuccess | Success [v] deriving (Eq, Ord, Show, Generic)
{-
will search to at most the depthLimit from the start, and will see at most nodeLimit nodes
searches from the given vertex to try to find "success" nodes. 
-}
dfs :: forall v. (Pretty v, Ord v) => Int -> Int -> (v -> [v]) -> (v -> Bool) -> v -> Either Text (SearchResult v)
dfs depthLimit nodeLimit getAdjacent isSuccess startVertex = munge $ loop True Empty [] [(0, startVertex)] where 
  munge :: (Bool, Either Text [v]) -> Either Text (SearchResult v)
  munge = \case 
    (_, Right path) -> Right (Success path)
    (True, Left _reason) -> Right NoSuccess 
    (False, Left reason) -> Left $ "search was not exhaustive and " <> reason 
  --explored nodes, the path from the start to here, and the stack of things to explore
  --the stack is a list of depths and a vertex at that depth
  loop :: Bool -> Set v -> [v] -> [(Int, v)] -> (Bool, Either Text [v])
  -- loop searchWasExhaustive explored curPath stack | 
  --    trace ("curStack: " <> show stack) False = undefined 
  loop searchWasExhaustive explored curPath stack = if length explored > nodeLimit then (False, Left "hit nodelimit") else 
    case stack of 
      [] -> (searchWasExhaustive, Left "ran out of things to search")
      (vDepth, v) : vs -> --trace ("exploring: " <> showP v) $
       let newPath = takeExact vDepth curPath ++ [v] in 
        if isSuccess v 
          then (searchWasExhaustive, Right newPath)
          else let 
              (newBool, newVertices) = if length newPath > depthLimit then (False, []) else
                (searchWasExhaustive, filter (not . flip S.member explored) $ getAdjacent v) in 
            loop newBool (S.insert v explored) newPath (((vDepth+1,) <$> newVertices) ++ vs) 

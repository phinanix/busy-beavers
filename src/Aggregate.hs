module Aggregate where 



import Relude
import Control.Lens hiding ((.=))
import qualified Relude.Unsafe as U
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Set as S
import qualified Data.List.NonEmpty as NE
import qualified Text.Show 
import Relude.Extra (bimapBoth)
import Prettyprinter
import Safe.Exact
import Control.Exception (assert)
import Safe.Partial

{-
goals: make a nice interface (DSL I suppose) for taking a single Foldable and computing 
summary statistics of it. I think you make a list of "stat" objects, and there's an 
executor which takes them and uses them to execute a foldl. 

stat objects: 
 - countMeetPredicate 
 - maximumBy
actually in general there are stats we want to run over a subset of the input, so 
perhaps it makes sense for an object to have a filter plus a statistic, and it 
computes the statistic on the subset that pass the filter
-}

data StatType a = Count | MaxKBy Int (a -> a -> Ordering) deriving Generic
type Filter a = a -> Bool 
data Statistic a = Statistic (Filter a) (StatType a) 

data StatsResult a = CountRes Int | MaxKByRes [a] deriving (Eq, Ord, Show, Generic) 
instance (NFData a) => NFData (StatsResult a)

initResult :: Statistic a -> StatsResult a 
initResult (Statistic _filter statType) = case statType of 
  Count -> CountRes 0 
  MaxKBy _ _ -> MaxKByRes []

insertMaxKBy :: Int -> (a -> a -> Ordering) -> a -> [a] -> [a]
insertMaxKBy k ord new prevBest = if length prevBest < k 
  then sortBy ord $ new : prevBest
  else takeExact k $ sortBy ord $ new : prevBest 

runStats :: (Foldable t) => [Statistic a] -> t a -> [(Statistic a, StatsResult a)]
runStats stats = foldl' addAll startVal 
  where 
  startVal = (\stat -> (stat, initResult stat)) <$> stats  
  addAll prevList new = addOne new <$> prevList
  addOne :: a -> (Statistic a, StatsResult a) -> (Statistic a, StatsResult a)
  addOne new same@(stat@(Statistic filter statOp), prevRes) = if filter new 
    then case (statOp, prevRes) of 
      (Count, CountRes n) -> (stat, CountRes $ n+1)
      (MaxKBy k ord, MaxKByRes prevBest) -> (stat, MaxKByRes $ insertMaxKBy k ord new prevBest) 
      _ -> error "stats didn't match statres"
    else same 
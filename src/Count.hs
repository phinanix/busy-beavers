module Count where

import Relude
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))

data Count = Count
  { num :: Natural
  , vars :: MonoidalMap Natural (Sum Natural)
  } deriving (Eq, Ord, Show, Generic)
instance NFData Count

instance Semigroup Count where
  (Count n vs) <> (Count m ws) = Count (n+m) (vs <> ws)

instance Monoid Count where
  mempty = Count 0 mempty

--this is actually the default instance
instance AsEmpty Count where
  _Empty = only mempty

--trying to match the first count against the second, returns Nothing on fail,
--or the remaining part of the second count on success
matchCount :: Count -> Count -> Maybe Count
--two numbers match if the first one is smaller
matchCount (Count n Empty) (Count m Empty) = if n <= m
  then Just (Count (m - n) Empty)
  else Nothing
--a number can't match something with vars
matchCount (Count _ Empty) (Count _ _not_empty) = Nothing
--something with vars can match a bare number or something with vars, as long as
--the numbers added to the vars are compatible
-- x can match y, and x can match x+1, but x+1 can't match z, because what if z = 1?
matchCount (Count n vs) (Count m ws) = if n <= m
  then Just (Count 0 Empty)
  else Nothing

finiteCount :: Natural -> Count
finiteCount n = Count n mempty

varCount :: Natural -> Count
varCount n = Count 0 $ MonoidalMap (one (n,Sum 1))

--fails when the equation is inconsistent with what we already know
addEquation :: (Count, Count) -> Map Count Count -> Maybe (Map Count Count)
addEquation (l, r) m = case m ^. at l of
  Nothing -> Just $ m & at l ?~ r
  Just r' -> guard (r == r') >> Just m

module Count where

import Relude
import Control.Lens
import Data.Map.Merge.Strict (mergeA, zipWithAMatched, preserveMissing)
import Data.Map.Monoidal (MonoidalMap(..), assocs)
import Data.Witherable

import Util

data Count = Count
  { num :: Natural
  , vars :: MonoidalMap Natural (Sum Natural)
  } deriving (Eq, Ord, Show, Generic)
instance NFData Count

dispCount :: Count -> Text
dispCount (Count n vars) = show n <> " + " <> (mconcat $ dispVar <$> assocs vars)

dispVar :: (Natural, Sum Natural) -> Text
dispVar (n, Sum count) =  show count <> "*x_" <> show n <> " "

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
matchCount (Count n _vs) (Count m _ws) = if n <= m
  then Just (Count 0 Empty)
  else Nothing

finiteCount :: Natural -> Count
finiteCount n = Count n mempty

varCount :: Natural -> Count
varCount n = Count 0 $ MonoidalMap (one (n,Sum 1))

--fails when the equation is inconsistent with what we already know
addEquationToMap :: (Count, Count) -> Map Count Count -> Maybe (Map Count Count)
addEquationToMap eqn m = case admissible eqn of
  WrongEqn -> Nothing
  Tautology -> Just m
  Equation (l,r) -> case m ^. at l of
    Nothing -> Just $ m & at l ?~ r
    Just r' -> guard (r == r') >> Just m

data EquationStatus = WrongEqn | Tautology | Equation (Count, Count) deriving (Eq, Ord, Show, Generic)
instance NFData EquationStatus

admissible :: (Count, Count) -> EquationStatus
admissible (Count m Empty, Count n Empty) | m == n = Tautology
admissible (Count m Empty, Count n Empty) | m /= n = WrongEqn
admissible eqn = Equation eqn

addEquation :: (Count, Count) -> EquationState a -> EquationState a
addEquation eqn (EquationState (Just (m, a))) = case addEquationToMap eqn m of
  Nothing -> EquationState Nothing
  (Just m') -> EquationState (Just (m',a))
addEquation _ _ = EquationState Nothing

mergeEqns :: Map Count Count -> Map Count Count -> Maybe (Map Count Count)
mergeEqns = mergeA preserveMissing preserveMissing
  (zipWithAMatched (\_k v1 v2 -> if v1 == v2 then Just v1 else Nothing))

newtype EquationState s = EquationState {getEquationState :: Maybe (Map Count Count, s)}
  deriving newtype (Eq, Ord, Show)

nothingES :: EquationState s
nothingES = EquationState Nothing

maybeES :: Maybe s -> EquationState s
maybeES = EquationState . fmap (Empty,)

mergeApp :: (Map Count Count, a -> b) -> (Map Count Count, a) -> Maybe (Map Count Count, b)
mergeApp (eqns, f) (moreEqns, a) = (, f a) <$> mergeEqns eqns moreEqns

instance Functor EquationState where
  fmap f (EquationState e) = EquationState $ fmap (fmap f) e
instance Applicative EquationState where
  pure s = EquationState $ Just (Empty, s)
  (EquationState f) <*> (EquationState a) = EquationState $ join $ mergeApp <$> f <*> a

instance Monad EquationState where
  (EquationState k) >>= f = EquationState $ bind combine $ getEquationState . f <$$> k
    where
    combine (eqns, Just (moreEqns, b)) = (,b) <$> mergeEqns eqns moreEqns
    combine (_, Nothing) = Nothing

instance MonadFail EquationState where
  fail _ = EquationState Nothing

instance Filterable EquationState where
  mapMaybe fm (EquationState (Just (eqns, a))) = EquationState $ (eqns,) <$> fm a
  mapMaybe _ (EquationState Nothing) = EquationState Nothing

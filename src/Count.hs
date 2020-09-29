module Count where

import Relude
import Control.Lens
import Data.Map.Merge.Strict (mergeA, zipWithAMatched, preserveMissing)
import Data.Map.Monoidal (MonoidalMap(..), assocs)
import Data.Foldable
import Data.Witherable

import Util

newtype SymbolVar = SymbolVar Int
  deriving (Eq, Ord, Show, Generic)
getSymbol :: SymbolVar -> Int
getSymbol (SymbolVar i) = i
instance NFData SymbolVar

dispSymbolVar :: (SymbolVar, Sum Natural) -> Text
dispSymbolVar (SymbolVar i, Sum count) = show count <> "*a_" <> show i <> " "

dispBoundVar :: (BoundVar, Sum Natural) -> Text
dispBoundVar (BoundVar i, Sum count) = show count <> "*x_" <> show i <> " "

newtype BoundVar = BoundVar Int
  deriving (Eq, Ord, Show, Generic)
getBoundVar :: BoundVar -> Int
getBoundVar (BoundVar i) = i
instance NFData BoundVar

data Count = Count
  { num :: Natural
  , symbols :: MonoidalMap SymbolVar (Sum Natural)
  , bound :: MonoidalMap BoundVar (Sum Natural)
  } deriving (Eq, Ord, Show, Generic)
instance NFData Count

dispCount :: Count -> Text
dispCount (Count n symbols bound)
  = show n <> " + "
  <> (mconcat $ dispSymbolVar <$> assocs symbols)
  <> (mconcat $ dispBoundVar <$> assocs bound)

instance Semigroup Count where
  (Count n as xs) <> (Count m bs ys) = Count (n+m) (as <> bs) (xs <> ys)

instance Monoid Count where
  mempty = Count 0 mempty mempty

--this is actually the default instance
instance AsEmpty Count where
  _Empty = only mempty

--trying to match the first count against the second, returns Nothing on fail,
--or the remaining part of the second count on success
matchCount :: Count -> Count -> Maybe Count
matchCount (Count 0 Empty xs) (Count m bs ys) = undefined
matchCount (Count 0 as xs) (Count m bs ys) = matchCount (Count 0 Empty xs) =<<
  (Count m <$> matchSymbolVarMap (assocs $ getSum <$> as) bs <*> pure ys) where
  -- matchSymbolVarMap :: [(SymbolVar, Natural)] -> MonoidalMap SymbolVar (Sum Natural)
  --   -> Maybe (MonoidalMap SymbolVar (Sum Natural))
  matchSymbolVarMap as bs = foldrM subtractSymbolVar bs as
  subtractSymbolVar :: (SymbolVar, Natural) -> MonoidalMap SymbolVar (Sum Natural)
    -> Maybe (MonoidalMap SymbolVar (Sum Natural))
  subtractSymbolVar (var, count) m = case m ^. at var of
    Nothing -> Nothing
    Just (Sum occurs) -> case compare count occurs of
      LT -> Just $ m & at var . _Just . _Wrapped' -~ count
      EQ -> Just $ m & at var .~ Nothing
      GT -> Nothing
--if the first count has a postive number, then we want to match it first
matchCount (Count n as xs) (Count m bs ys) = if n <= m
  then matchCount (Count 0 as xs) (Count (m-n) bs ys)
  else Nothing
-- --a number can't match something with vars
-- matchCount (Count _ Empty) (Count _ _not_empty) = Nothing
-- --something with vars can match a bare number or something with vars, as long as
-- --the numbers added to the vars are compatible
-- -- x can match y, and x can match x+1, but x+1 can't match z, because what if z = 1?
-- matchCount (Count n _vs) (Count m _ws) = if n <= m
--   then Just (Count 0 Empty)
--   else Nothing

finiteCount :: Natural -> Count
finiteCount n = Count n mempty mempty

symbolicVarCount :: Int -> Count
symbolicVarCount n = Count 0 (MonoidalMap (one (SymbolVar n, Sum 1))) mempty

boundVarCount :: Int -> Count
boundVarCount n = Count 0 mempty $ MonoidalMap (one (BoundVar n, Sum 1))

-- --fails when the equation is inconsistent with what we already know
-- addEquationToMap :: (Count, Count) -> Map Count Count -> Maybe (Map Count Count)
-- addEquationToMap (Count _ Empty, _) m = Just m
-- addEquationToMap eqn m = case admissible eqn of
--   WrongEqn -> Nothing
--   Tautology -> Just m
--   Equation (l,r) -> case m ^. at l of
--     Nothing -> Just $ m & at l ?~ r
--     Just r' -> guard (r == r') >> Just m
--
-- data EquationStatus = WrongEqn | Tautology | Equation (Count, Count) deriving (Eq, Ord, Show, Generic)
-- instance NFData EquationStatus

-- --TODO:: this is commented out because I think it's wrong - we're allowed to match
-- --only part of the point for example (5 against 7)
-- admissible :: (Count, Count) -> EquationStatus
-- -- admissible (Count m Empty, Count n Empty) | m == n = Tautology
-- -- admissible (Count m Empty, Count n Empty) | m /= n = WrongEqn
-- admissible eqn = Equation eqn
--
-- --TODO :: this logic needs to be seriously reworked, I think it is like very broken currently
-- addEquation :: (Count, Count) -> EquationState a -> EquationState a
-- addEquation eqn (EquationState (Just (m, a))) = case addEquationToMap eqn m of
--   Nothing -> undefined --EquationState Nothing
--   (Just m') -> EquationState (Just (m',a))
-- addEquation _ _ = undefined --EquationState Nothing
--
-- mergeEqns :: Map Count Count -> Map Count Count -> Maybe (Map Count Count)
-- mergeEqns = mergeA preserveMissing preserveMissing
--   (zipWithAMatched (\_k v1 v2 -> if v1 == v2 then Just v1 else undefined)) --Nothing))
--
-- newtype EquationState s = EquationState {getEquationState :: Maybe (Map Count Count, s)}
--   deriving newtype (Eq, Ord, Show)
--
-- runEquationState :: EquationState s -> Maybe s
-- runEquationState = fmap snd . getEquationState
--
-- nothingES :: EquationState s
-- nothingES = EquationState Nothing
--
-- maybeES :: Maybe s -> EquationState s
-- maybeES = EquationState . fmap (Empty,)
--
-- mergeApp :: (Map Count Count, a -> b) -> (Map Count Count, a) -> Maybe (Map Count Count, b)
-- mergeApp (eqns, f) (moreEqns, a) = (, f a) <$> mergeEqns eqns moreEqns
--
-- instance Functor EquationState where
--   fmap f (EquationState e) = EquationState $ fmap (fmap f) e
-- instance Applicative EquationState where
--   pure s = EquationState $ Just (Empty, s)
--   (EquationState f) <*> (EquationState a) = EquationState $ join $ mergeApp <$> f <*> a
--
-- instance Monad EquationState where
--   (EquationState k) >>= f = EquationState $ bind combine $ getEquationState . f <$$> k
--     where
--     combine (eqns, Just (moreEqns, b)) = (,b) <$> mergeEqns eqns moreEqns
--     combine (_, Nothing) = Nothing
--
-- instance MonadFail EquationState where
--   fail _ = EquationState Nothing
--
-- instance Filterable EquationState where
--   mapMaybe fm (EquationState (Just (eqns, a))) = EquationState $ (eqns,) <$> fm a
--   mapMaybe _ (EquationState Nothing) = EquationState Nothing

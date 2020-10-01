module Count where

import Relude hiding (filter)
import qualified Relude.Unsafe as Unsafe (head)
import Control.Lens
import qualified Data.Map as M (assocs)
import Data.Map.Merge.Strict (mergeA, zipWithAMatched, preserveMissing)
import Data.Map.Monoidal (MonoidalMap(..), assocs, mapKeys, unionWith, partitionWithKey)
import Data.Foldable
import Data.Witherable

import Util

--a variable with logical type positive integer which is "undergoing universal
-- generalization" - when you step inside the ∀x . Q(x), the x
newtype SymbolVar = SymbolVar Int
  deriving (Eq, Ord, Show, Generic)
getSymbol :: SymbolVar -> Int
getSymbol (SymbolVar i) = i
instance NFData SymbolVar

--a variable with logical type positive integer which is (implicitly) quantified
-- / bound by a forall quantifier at the beginning of the sentence
newtype BoundVar = BoundVar Int
  deriving (Eq, Ord, Show, Generic)
getBoundVar :: BoundVar -> Int
getBoundVar (BoundVar i) = i
instance NFData BoundVar

--a variable with logical type "s", the type variable of symbols on the tape which
--is implicitly forall quantified
newtype TapeVar = TapeVar Int
  deriving (Eq, Ord, Show, Generic)
getTapeVar :: TapeVar -> Int
getTapeVar (TapeVar i) = i
instance NFData TapeVar

dispSymbolVar :: (SymbolVar, Sum Natural) -> Text
dispSymbolVar (SymbolVar i, Sum count) = show count <> "*a_" <> show i <> " "

dispBoundVar :: (BoundVar, Sum Natural) -> Text
dispBoundVar (BoundVar i, Sum count) = show count <> "*x_" <> show i <> " "

dispTapeVar :: TapeVar -> Text
dispTapeVar (TapeVar i) = "t_" <> show i <> " "

data VarOr s = Var TapeVar | NotVar s deriving (Eq, Ord, Show, Generic)
instance NFData s => NFData (VarOr s)
$(makePrisms ''VarOr)

--returns () because if the match fails, the ES can just fail the whole computation
matchTapeVar :: (Eq s) => VarOr s -> s -> EquationState s ()
matchTapeVar (Var v) s = addTapeVar (v, s) $ pure ()
matchTapeVar (NotVar t) s = maybeES $ guard (t == s)

data Count = Count
  { num :: Natural
  , symbols :: MMap SymbolVar (Sum Natural)
  , bound :: MMap BoundVar (Sum Natural)
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

nTimesCount :: (Integral n) => n -> Count -> Count
nTimesCount n c = fold $ genericReplicate n c

maybeDiv :: (Integral a) => a -> a -> Maybe a
maybeDiv n d = if n `mod` d == 0 then Just $ n `div` d else Nothing

divMap :: MMap k (Sum Natural) -> Natural -> Maybe (MMap k (Sum Natural))
divMap m d = Sum <$$> traverse (flip maybeDiv d) (getSum <$> m)

divCount :: Count -> Natural -> Maybe Count
divCount (Count n as xs) d = Count <$> (n `maybeDiv` d) <*> (as `divMap` d) <*> (xs `divMap` d)

--trying to match the first count against the second, returns Nothing on fail,
--or the remaining part of the second count on success
matchCount :: (Eq s) => Count -> Count -> EquationState s Count
matchCount Empty c = pure c
matchCount (Count 0 Empty xs) c@(Count m bs ys) = case assocs xs of
  [] -> error "xs can't be empty due to pattern match"
  --if there's only one var, then it has to be the case that the RHS is a multiple
  --of the count of that var, and there's only one way to match
  [(x, Sum d)] -> case divCount c d of
    Nothing -> nothingES
    Just reducedC -> addEquation (x, reducedC) $ pure Empty
  xs -> case containsOne xs of
    (maybeX1, xs') -> foldrM matchVar (eitherKeys bs ys, []) xs' >>= \case
      --now we've matched all the vars we can against other vars, so we proceed
      --assuming the only way for the match to succeed is if the remaining vars
      --on the LHS are mapped to 1
      --that requires that we have m big enough for that to actually work
      (unEitherKeys -> (newBs, newYs), remaining) ->
        let remainingSum = getSum $ foldMap snd remaining in
        if remainingSum > m then nothingES else
        --we need to do two things here: first, send all the remaining vars to one,
        --second send x1 to everything else
        addEquations ((,finiteCount 1) . fst <$> remaining) $ case maybeX1 of
          Just x1 -> addEquation (x1, Count (m - remainingSum) newBs newYs) $
            --the leftovers are empty because x1 matched everything
            pure $ Empty
          --there's some stuff leftover because there was no x1 to eat it all
          --TODO:: we might could do better in this case but it seems hard
          Nothing -> pure $ Count (m - remainingSum) newBs newYs

  where
  eitherKeys :: (Ord k, Ord j) => MMap k v -> MMap j v -> MMap (Either k j) v
  eitherKeys xs ys = unionWith (error "either can't collide") (mapKeys Left xs) (mapKeys Right ys)
  unEitherKeys :: (Ord k, Ord j) => MMap (Either k j) v -> (MMap k v, MMap j v)
  unEitherKeys = bimap (mapKeys unsafeFromLeft) (mapKeys unsafeFromRight) . partitionWithKey (curry $ has _Left . fst)

  --takes a list and pulls out first element that satisfies the predicate
  --the second list is the original list, minus the pulled out element, or the
  --original list unchanged if there is no satisfying element
  containsOne :: [(k, Sum Natural)] -> (Maybe k, [(k, Sum Natural)])
  containsOne xs = (maybeK, rest) where
    maybeK = fst <$> listToMaybe bs
    (as, bs) = break ((== Sum 1) . snd) xs
    rest = case maybeK of
      Nothing -> xs
      Just _ -> as ++ drop 1 bs
  --takes a var, and tries to match it with a symbol in the map. if it succeeds, it
  --removes that symbol from the map and returns the list unchanged. if it fails, it
  --adds the var to the list to be handled later.
  matchVar :: (Eq s) => (BoundVar, Sum Natural)
    -> (MMap (Either SymbolVar BoundVar) (Sum Natural), [(BoundVar, Sum Natural)])
    -> EquationState s (MMap (Either SymbolVar BoundVar) (Sum Natural), [(BoundVar, Sum Natural)])
  matchVar var@(x, Sum d) (m, rest) =
    case listToMaybe $ filter (\(_y, Sum  e) -> e `mod` d == 0) $ assocs m of
      --no var in the map works here
      Nothing -> pure $ (m, var:rest)
      --here y works, so we need to delete it, but we also need to emit the new eqn
      Just (y, Sum e) ->
        let newM = m & at y .~ Nothing
            eqn = (x, makeCount y $ e `div` d) in
          addEquation eqn $ pure (newM, rest)
  makeCount :: (Either SymbolVar BoundVar) -> Natural -> Count
  makeCount (Left symbol) d = symbolVarCount symbol d
  makeCount (Right bound) d = boundVarCount bound d
--if the LHS has symbolic vars, they must also appear on the RHS or the match will fail
matchCount (Count 0 as xs) (Count m bs ys)
  = matchCount leftCount =<< maybeRightCount where
    leftCount = Count 0 Empty xs
    maybeRightCount = Count m <$> matchSymbolVarMap (getSum <$> as) bs <*> pure ys
    matchSymbolVarMap as bs = ifoldrM subtractSymbolVar bs as
    subtractSymbolVar var count m = case m ^. at var of
      Nothing -> nothingES
      Just (Sum occurs) -> case compare count occurs of
        LT -> pure $ m & at var . _Just . _Wrapped' -~ count
        EQ -> pure $ m & at var .~ Nothing
        GT -> nothingES
--if the first count has a postive number, then we want to match it first
matchCount (Count n as xs) (Count m bs ys) = if n <= m
  then matchCount (Count 0 as xs) (Count (m-n) bs ys)
  else nothingES


finiteCount :: Natural -> Count
finiteCount n = Count n mempty mempty

symbolVarCount :: SymbolVar -> Natural -> Count
symbolVarCount a d = Count 0 (MonoidalMap (one (a, Sum d))) mempty

boundVarCount :: BoundVar -> Natural -> Count
boundVarCount x d = Count 0 mempty (MonoidalMap (one (x, Sum d)))

newBoundVar :: Int -> Count
newBoundVar n = Count 0 mempty $ MonoidalMap (one (BoundVar n, Sum 1))

--fails when the equation is inconsistent with what we already know
addEquationToMap :: (BoundVar, Count) -> Map BoundVar Count -> Maybe (Map BoundVar Count)
addEquationToMap (v, c) m = case m ^. at v of
  Nothing -> Just $ m & at v ?~ c
  --it's fine to assign the same count twice, but fails immediately if you assign
  --the same var to a new count. This is where we'd need to emit info to backtrack
  --if that ends up being a good feature to do
  Just c' -> guard (c == c') >> Just m

addEquation :: (BoundVar, Count) -> EquationState s a -> EquationState s a
addEquation eqn (EquationState (Just (m, vs, a))) = case addEquationToMap eqn m of
  Nothing -> EquationState Nothing
  (Just m') -> EquationState (Just (m', vs, a))
addEquation _ _ = EquationState Nothing

addEquations :: (Foldable t) => t (BoundVar, Count) -> EquationState s a -> EquationState s a
addEquations = appEndo . foldMap (Endo . addEquation)

mergeEqns :: Map BoundVar Count -> Map BoundVar Count -> Maybe (Map BoundVar Count)
mergeEqns = mergeA preserveMissing preserveMissing
  (zipWithAMatched (\_k v1 v2 -> if v1 == v2 then Just v1 else Nothing))

addTapeVarToMap :: (Eq s) => (TapeVar, s) -> Map TapeVar s -> Maybe (Map TapeVar s)
addTapeVarToMap (var, b) m = case m ^. at var of
  Nothing -> Just $ m & at var ?~ b
  Just b' -> guard (b == b') >> Just m

addTapeVar :: (Eq s) => (TapeVar, s) -> EquationState s a -> EquationState s a
addTapeVar eqn (EquationState (Just (m, vs, a))) = case addTapeVarToMap eqn vs of
  Nothing -> nothingES
  (Just vs') -> EquationState (Just (m, vs', a))
addTapeVar _ _ = nothingES

addTapeVars :: (Foldable t, Eq s) => t (TapeVar, s) -> EquationState s a -> EquationState s a
addTapeVars = appEndo . foldMap (Endo . addTapeVar)

mergeTapeVars :: (Eq s) => Map TapeVar s -> Map TapeVar s -> Maybe (Map TapeVar s)
mergeTapeVars (M.assocs -> newEqns)
  = (appEndo . mconcat $ Endo <$> (bind <$> (addTapeVarToMap <$> newEqns))) . Just

newtype EquationState s a = EquationState
  {runEquationState :: Maybe (Map BoundVar Count, Map TapeVar s, a)}
  deriving newtype (Eq, Ord, Show)

getEquationState :: EquationState s a -> Maybe a
getEquationState = fmap (view _3) . runEquationState

nothingES :: EquationState s a
nothingES = EquationState Nothing

maybeES :: Maybe a -> EquationState s a
maybeES = EquationState . fmap (Empty, Empty,)

instance Functor (EquationState s) where
  fmap f (EquationState e) = EquationState $ fmap (fmap f) e
instance (Eq s) => Applicative (EquationState s) where
  pure s = EquationState $ Just (Empty, Empty, s)
  (EquationState f) <*> (EquationState a) = EquationState $ join $ mergeApp <$> f <*> a where
    mergeApp (eqns, vs, f) (moreEqns, moreVs, a)
      = (,, f a) <$> mergeEqns eqns moreEqns <*> mergeTapeVars vs moreVs

instance (Eq s) => Monad (EquationState s) where
  (EquationState k) >>= f = EquationState $ bind combine $ runEquationState . f <$$> k
    where
    combine (eqns, vs, Just (moreEqns, moreVs, b))
      = (,,b) <$> mergeEqns eqns moreEqns <*> mergeTapeVars vs moreVs
    combine (_, _, Nothing) = Nothing

instance (Eq s) => MonadFail (EquationState s) where
  fail _ = EquationState Nothing

instance Filterable (EquationState s) where
  mapMaybe fm (EquationState (Just (eqns, vs, a))) = EquationState $ (eqns,vs,) <$> fm a
  mapMaybe _ (EquationState Nothing) = EquationState Nothing

module Count where

import Relude hiding (filter, mapMaybe)
import qualified Text.Show
import qualified Relude.Unsafe as Unsafe (head)
import Control.Lens
import qualified Data.Map as M (assocs)
import Data.Map.Merge.Strict (mergeA, zipWithAMatched, preserveMissing)
import Data.Map.Monoidal (MonoidalMap(..), assocs, mapKeys, unionWith, size, singleton,
  partitionWithKey, keys, intersectionWith)
import Data.Foldable
import Witherable
import Data.Biapplicative

import Util
import Prettyprinter
import Safe.Partial
import Relude.Extra (bimapBoth)
import Data.Aeson

--a variable with logical type positive integer which is "undergoing universal
-- generalization" - when you step inside the ∀x . Q(x), the x
newtype SymbolVar = SymbolVar Int
  deriving (Eq, Ord, Show, Generic)
getSymbol :: SymbolVar -> Int
getSymbol (SymbolVar i) = i
instance NFData SymbolVar
instance ToJSONKey SymbolVar
instance ToJSON SymbolVar where 
  toEncoding = genericToEncoding defaultOptions
instance FromJSONKey SymbolVar where 
instance FromJSON SymbolVar where 

--a variable with logical type positive integer which is (implicitly) quantified
-- / bound by a forall quantifier at the beginning of the sentence
newtype BoundVar = BoundVar Int
  deriving (Eq, Ord, Show, Generic)
getBoundVar :: BoundVar -> Int
getBoundVar (BoundVar i) = i
instance NFData BoundVar
instance ToJSONKey BoundVar
instance ToJSON BoundVar where 
  toEncoding = genericToEncoding defaultOptions
instance FromJSONKey BoundVar where 
instance FromJSON BoundVar where 

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

-- a class that currently generalizes over Count and InfCount, which both have counts that are the "unit"
-- not sure there are any laws here other than that when your location is One your count is the unit
class (Monoid c) => Countable c where
  unit :: c

--a finite number, plus some number of symbols multiplied by a given natural (which must be positive)
--and some number of bound variables also multiplied by a given natural which also must be positive
data Count = Count
  { num :: Natural
  , symbols :: MMap SymbolVar (Sum Natural)
  , bound :: MMap BoundVar (Sum Natural)
  } deriving (Eq, Generic)
instance NFData Count
instance ToJSON a => ToJSON (Sum a) where
  toEncoding = genericToEncoding defaultOptions
instance FromJSON a => FromJSON (Sum a) where
instance ToJSON Count where 
  toEncoding = genericToEncoding defaultOptions
instance FromJSON Count 

pattern One :: Count
pattern One = Count 1 Empty Empty

pattern FinCount :: Natural -> Count
pattern FinCount n = Count n Empty Empty

instance Show Count where
  show (Count num symbols bound) = "Count " <> show num <> " (fromList " <> show (assocs symbols)
    <> ") (fromList " <> show (assocs bound) <> ")"

instance Countable Count where
  unit = finiteCount 1

pattern ZeroVar :: Natural -> MMap SymbolVar (Sum Natural) -> Count
pattern ZeroVar n as = Count n as Empty

pattern SingletonMap :: k -> v -> MMap k v
pattern SingletonMap k v <- (assocs -> [(k,v)]) where
  SingletonMap k v = singleton k v

pattern OneVar :: Natural -> MMap SymbolVar (Sum Natural) -> Natural -> BoundVar -> Count
pattern OneVar n as k x = Count n as (SingletonMap x (Sum k))

--bound vars bigger than free vars bigger than bare numbers
--if both have bounds or frees, then compare via summing coefficients
instance Ord Count where
  (Count n Empty Empty) <= (Count m Empty Empty) = n <= m
  (Count _ Empty Empty) <= (Count _ _ne Empty) = True
  c@(Count n as Empty) <= d@(Count m bs Empty)
    | c == d = True
    | fold as < fold bs = True
    | otherwise = case compare n m of
      LT -> True
      GT -> False
      EQ -> as < bs
  (Count _ _ Empty) <= (Count _ _ _ne) = True
  --hang, on, I'm worried this ord instance isn't compatible with the semigroup
  --I now think it is but still want like, a proof TODO
  c@(Count n as xs) <= d@(Count m bs ys)
    | c == d = True
    | fold xs < fold ys = True
    | otherwise = case compare (Count n as Empty) (Count m bs Empty) of
      LT -> True
      GT -> False
      EQ -> xs < ys

dispCount :: Count -> Text
dispCount (Count n Empty Empty) = show n
dispCount (Count n symbols bound)
  = show n <> " + "
  <> mconcat (dispSymbolVar <$> assocs symbols)
  <> mconcat (dispBoundVar <$> assocs bound)

instance Pretty Count where
  pretty = pretty . dispCount

--a count which has the potential to be "infinity" eg the infinite string of zeros at the
--end of a Turing Machine's tape
--infinity comes second so it's bigger than NotInfinity
data InfCount = NotInfinity Count | Infinity deriving (Eq, Ord, Show, Generic)
instance NFData InfCount
instance ToJSON InfCount where 
  toEncoding = genericToEncoding defaultOptions
instance FromJSON InfCount 

pattern IOne :: InfCount
pattern IOne = NotInfinity One

instance Countable InfCount where
  unit = NotInfinity unit

dispInfCount :: InfCount -> Text
dispInfCount Infinity = "inf"
dispInfCount (NotInfinity c) = dispCount c

instance Pretty InfCount where
  pretty = pretty . dispInfCount

countToMaybeInt :: Count -> Maybe Int
countToMaybeInt (Count m Empty Empty) = Just $ fromIntegral m
countToMaybeInt _c = Nothing 

infCountToMaybeInt :: InfCount -> Maybe Int
infCountToMaybeInt Infinity = Nothing 
infCountToMaybeInt (NotInfinity c) = countToMaybeInt c

countToInt :: HasCallStack => Count -> Int
countToInt (Count m Empty Empty) = fromIntegral m
countToInt c = error $ "tried to int-ify: " <> dispCount c

infCountToInt :: HasCallStack => InfCount -> Int
infCountToInt Infinity = error "infinity isn't an int"
infCountToInt (NotInfinity c) = countToInt c

deInfCount :: InfCount -> Count
deInfCount = \case
  Infinity -> error "deinfcount"
  NotInfinity c -> c

--the linear count, plus a series of counts put through the quadratic function
--f(x) = x(x+1) / 2, all summed
data QuadCount = QuadCount
  { _linearCount :: Count
  , _quadCounts :: [Count]
  } deriving (Eq, Ord, Show, Generic)

instance Semigroup Count where
  (Count n as xs) <> (Count m bs ys) = Count (n+m) (as <> bs) (xs <> ys)

instance Monoid Count where
  mempty = Count 0 mempty mempty

instance AsEmpty Count

instance Semigroup InfCount where
  Infinity <> _ = Infinity
  _ <> Infinity = Infinity
  (NotInfinity c) <> (NotInfinity d) = NotInfinity (c <> d)

instance Monoid InfCount where
  mempty = NotInfinity mempty

instance AsEmpty InfCount

instance Semigroup QuadCount where
  (QuadCount c qs) <> (QuadCount d rs) = QuadCount (c <> d) (qs <> rs)

instance Monoid QuadCount where
  mempty = QuadCount mempty mempty

instance AsEmpty QuadCount

nTimes :: (Integral n, Monoid m) => n -> m -> m
nTimes n x = fold $ genericReplicate n x

maybeDiv :: (Integral a) => a -> a -> Maybe a
maybeDiv n d = if n `mod` d == 0 then Just $ n `div` d else Nothing

divMap :: MMap k (Sum Natural) -> Natural -> Maybe (MMap k (Sum Natural))
divMap m d = Sum <$$> traverse (flip maybeDiv d) (getSum <$> m)

divCount :: Count -> Natural -> Maybe Count
divCount (Count n as xs) d = Count <$> (n `maybeDiv` d) <*> (as `divMap` d) <*> (xs `divMap` d)

divRem :: Natural -> Natural -> (Natural, Natural)
divRem n d = (n `div` d, n `mod` d)

divRemMap :: MMap k (Sum Natural) -> Natural -> (MMap k (Sum Natural), MMap k (Sum Natural))
divRemMap m d = (fst <$> pairMap, snd <$> pairMap) where
  pairMap = bimapBoth Sum . (`divRem` d) . getSum <$> m

--quotient, remainder
divRemCount :: Count -> Natural -> (Count, Count)
divRemCount (Count n as xs) d = bimapBoth Count (n `divRem` d) <<*>> (as `divRemMap` d) <<*>> (xs `divRemMap` d)

divRemInfCount :: InfCount -> Natural -> (InfCount, InfCount) 
divRemInfCount ic d = case ic of 
  Infinity -> (Infinity, Infinity) 
  NotInfinity c -> bimapBoth NotInfinity $ divRemCount c d 

subNatFromCount :: Count -> Natural -> Maybe Count
subNatFromCount (Count n as xs) m = guard (n >= m) $> Count (n - m) as xs

unsafeSubNatFromCount :: Count -> Natural -> Count
unsafeSubNatFromCount c n = case subNatFromCount c n of
  Nothing -> error $ "unsafesubnatfromcount " <> show c
  Just r -> r

subCountFromCount :: Count -> Count -> Maybe Count
--if the second count is fully present in the first count, then there will be no leftovers from the second count
subCountFromCount c d = case likeTerms c d of
  (_, res, Empty) -> Just res
  _ -> Nothing

subInfCountFromInfCount :: InfCount -> InfCount -> Maybe InfCount 
subInfCountFromInfCount ci di = case (ci, di) of 
  (Infinity, _) -> Just Infinity
  (NotInfinity _, Infinity) -> Nothing 
  (NotInfinity c, NotInfinity d) -> NotInfinity <$> subCountFromCount c d 

unsafeSubCountFromCount :: Partial => Count -> Count -> Count
unsafeSubCountFromCount = fmap (fmap fromJust) subCountFromCount

unsafeSubInfCountFromInfCount :: Partial => InfCount -> InfCount -> InfCount 
unsafeSubInfCountFromInfCount = fmap (fmap fromJust) subInfCountFromInfCount

normMap :: (Monoid m, Eq m) => MMap k m -> MMap k m
normMap = MonoidalMap . mapMaybe (\x -> if x == mempty then Nothing else Just x)  . getMonoidalMap

normCount :: Count -> Count
normCount (Count n as xs) = Count n (normMap as) (normMap xs)

--given two counts, returns a count of their like terms and the two leftovers, in that order 
likeTerms :: Count -> Count -> (Count, Count, Count)
likeTerms (Count n as xs) (Count m bs ys) = (likes, leftOvers, rightOvers) where
  likeN = min n m
  combineNats (Sum n) (Sum m) = Sum $ min n m
  -- likeAs :: MMap SymbolVar (Sum Natural)
  likeAs = intersectionWith combineNats as bs
  -- likeXs :: MMap BoundVar (Sum Natural)
  likeXs = intersectionWith combineNats xs ys
  likes = Count likeN likeAs likeXs

  subMaps :: (Ord k, Num a, Monoid a, Eq a) => MMap k a -> MMap k a -> MMap k a
  subMaps = fmap (fmap normMap) $ unionWith (-)
  leftOvers = Count (n - likeN) (subMaps as likeAs) (subMaps xs likeXs)
  rightOvers = Count (m - likeN) (subMaps bs likeAs) (subMaps ys likeXs)

likeTermsInf :: InfCount -> InfCount -> (InfCount, InfCount, InfCount) 
likeTermsInf ic id = case (ic, id) of 
  (Infinity, Infinity) -> (Infinity, Empty, Empty)
  (Infinity, NotInfinity d) -> (NotInfinity d, Infinity, Empty) 
  (NotInfinity c, Infinity) -> (NotInfinity c, Empty, Infinity) 
  (NotInfinity c, NotInfinity d) -> let (likes, lOs, rOs) = likeTerms c d in 
    (NotInfinity likes, NotInfinity lOs, NotInfinity rOs)


removeCommonConsts :: Count -> Count -> Equations (MMap BoundVar (Sum Natural), Count)
removeCommonConsts (Count 0 as xs) (Count m bs ys)
  = (xs,) <$> maybeRightCount where
    maybeRightCount = Count m <$> rightSymbolVarMap <*> pure ys
    rightSymbolVarMap :: Equations (MMap SymbolVar (Sum Natural))
    rightSymbolVarMap = matchSymbolVarMap (getSum <$> as) bs
    matchSymbolVarMap :: MMap SymbolVar Natural -> MMap SymbolVar (Sum Natural) -> Equations (MMap SymbolVar (Sum Natural))
    matchSymbolVarMap as bs = ifoldrM subtractSymbolVar bs as
    subtractSymbolVar :: SymbolVar -> Natural -> MMap SymbolVar (Sum Natural) -> Equations (MMap SymbolVar (Sum Natural))
    subtractSymbolVar var count m = case m ^. at var of
      Nothing -> nothingES ""
      Just (Sum occurs) -> case compare count occurs of
        LT -> pure $ m & at var . _Just . _Wrapped' -~ count
        EQ -> pure $ m & at var .~ Nothing
        GT -> nothingES ""
--if the first count has a postive number, then we want to match it first
removeCommonConsts (Count n as xs) (Count m bs ys) = if n <= m
  then removeCommonConsts (Count 0 as xs) (Count (m-n) bs ys)
  else nothingES "matched a count with a bigger nat to a smaller nat"

removeCommonConstsInf :: Count -> InfCount -> Equations (MMap BoundVar (Sum Natural), InfCount)
removeCommonConstsInf (Count _n _as xs) Infinity = pure (xs, Infinity)
removeCommonConstsInf c (NotInfinity d) = NotInfinity <$$> removeCommonConsts c d 

matchVars :: MMap BoundVar (Sum Natural) -> Count -> Equations Count
matchVars xs c@(Count m bs ys) = case assocs xs of
  [] -> pure c
  --if there's only one var, then it has to be the case that the RHS is a multiple
  --of the count of that var, and there's only one way to match
  [(x, Sum d)] -> case divCount c d of
    Nothing -> nothingES "tried to divCount 1 var and vailed"
    Just Empty -> nothingES "cannot send a variable to zero"
    Just reducedC -> addEquation (x, NotInfinity reducedC) $ pure Empty
  xs -> trace "Warning: matchcount might send to zero" $ case containsOne xs of
    --TODO, we might send a variable to zero in here
    (maybeX1, xs') -> foldrM matchVar (eitherKeys bs ys, []) xs' >>= \case
      --now we've matched all the vars we can against other vars, so we proceed
      --assuming the only way for the match to succeed is if the remaining vars
      --on the LHS are mapped to 1
      --that requires that we have m big enough for that to actually work
      (unEitherKeys -> (newBs, newYs), remaining) ->
        let remainingSum = getSum $ foldMap snd remaining in
        if remainingSum > m then nothingES "ran out of nat" else
        --we need to do two things here: first, send all the remaining vars to one,
        --second send x1 to everything else
        addEquations ((,NotInfinity $ finiteCount 1) . fst <$> remaining) $ case maybeX1 of
          Just x1 -> addEquation (x1, NotInfinity $ Count (m - remainingSum) newBs newYs) $
            --the leftovers are empty because x1 matched everything
            pure Empty
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
  matchVar :: (BoundVar, Sum Natural)
    -> (MMap (Either SymbolVar BoundVar) (Sum Natural), [(BoundVar, Sum Natural)])
    -> Equations (MMap (Either SymbolVar BoundVar) (Sum Natural), [(BoundVar, Sum Natural)])
  matchVar var@(x, Sum d) (m, rest) =
    case find (\(_y, Sum  e) -> e `mod` d == 0) (assocs m) of
      --no var in the map works here
      Nothing -> pure (m, var:rest)
      --here y works, so we need to delete it, but we also need to emit the new eqn
      Just (y, Sum e) ->
        let newM = m & at y .~ Nothing
            eqn = (x, NotInfinity $ makeCount y $ e `div` d) in
          addEquation eqn $ pure (newM, rest)
  makeCount :: Either SymbolVar BoundVar -> Natural -> Count
  makeCount (Left symbol) d = symbolVarCount symbol d
  makeCount (Right bound) d = boundVarCount bound d


--trying to match the first count against the second, returns Nothing on fail,
--or the remaining part of the second count on success
matchCount :: Count -> Count -> Equations Count
matchCount c d = do
  (m, dRem) <- removeCommonConsts c d
  matchVars m dRem

-- matchCount Empty c = pure c
-- matchCount (Count 0 Empty xs) c@(Count m bs ys) = case assocs xs of
--   [] -> error "xs can't be empty due to pattern match"
--   --if there's only one var, then it has to be the case that the RHS is a multiple
--   --of the count of that var, and there's only one way to match
--   [(x, Sum d)] -> case divCount c d of
--     Nothing -> nothingES "tried to divCount 1 var and vailed"
--     Just Empty -> nothingES "cannot send a variable to zero"
--     Just reducedC -> addEquation (x, NotInfinity reducedC) $ pure Empty
--   xs -> trace "Warning: matchcount might send to zero" $ case containsOne xs of
--     --TODO, we might send a variable to zero in here
--     (maybeX1, xs') -> foldrM matchVar (eitherKeys bs ys, []) xs' >>= \case
--       --now we've matched all the vars we can against other vars, so we proceed
--       --assuming the only way for the match to succeed is if the remaining vars
--       --on the LHS are mapped to 1
--       --that requires that we have m big enough for that to actually work
--       (unEitherKeys -> (newBs, newYs), remaining) ->
--         let remainingSum = getSum $ foldMap snd remaining in
--         if remainingSum > m then nothingES "ran out of nat" else
--         --we need to do two things here: first, send all the remaining vars to one,
--         --second send x1 to everything else
--         addEquations ((,NotInfinity $ finiteCount 1) . fst <$> remaining) $ case maybeX1 of
--           Just x1 -> addEquation (x1, NotInfinity $ Count (m - remainingSum) newBs newYs) $
--             --the leftovers are empty because x1 matched everything
--             pure Empty
--           --there's some stuff leftover because there was no x1 to eat it all
--           --TODO:: we might could do better in this case but it seems hard
--           Nothing -> pure $ Count (m - remainingSum) newBs newYs

--   where
--   eitherKeys :: (Ord k, Ord j) => MMap k v -> MMap j v -> MMap (Either k j) v
--   eitherKeys xs ys = unionWith (error "either can't collide") (mapKeys Left xs) (mapKeys Right ys)
--   unEitherKeys :: (Ord k, Ord j) => MMap (Either k j) v -> (MMap k v, MMap j v)
--   unEitherKeys = bimap (mapKeys unsafeFromLeft) (mapKeys unsafeFromRight) . partitionWithKey (curry $ has _Left . fst)

--   --takes a list and pulls out first element that satisfies the predicate
--   --the second list is the original list, minus the pulled out element, or the
--   --original list unchanged if there is no satisfying element
--   containsOne :: [(k, Sum Natural)] -> (Maybe k, [(k, Sum Natural)])
--   containsOne xs = (maybeK, rest) where
--     maybeK = fst <$> listToMaybe bs
--     (as, bs) = break ((== Sum 1) . snd) xs
--     rest = case maybeK of
--       Nothing -> xs
--       Just _ -> as ++ drop 1 bs
--   --takes a var, and tries to match it with a symbol in the map. if it succeeds, it
--   --removes that symbol from the map and returns the list unchanged. if it fails, it
--   --adds the var to the list to be handled later.
--   matchVar :: (BoundVar, Sum Natural)
--     -> (MMap (Either SymbolVar BoundVar) (Sum Natural), [(BoundVar, Sum Natural)])
--     -> Equations (MMap (Either SymbolVar BoundVar) (Sum Natural), [(BoundVar, Sum Natural)])
--   matchVar var@(x, Sum d) (m, rest) =
--     case listToMaybe $ filter (\(_y, Sum  e) -> e `mod` d == 0) $ assocs m of
--       --no var in the map works here
--       Nothing -> pure $ (m, var:rest)
--       --here y works, so we need to delete it, but we also need to emit the new eqn
--       Just (y, Sum e) ->
--         let newM = m & at y .~ Nothing
--             eqn = (x, NotInfinity $ makeCount y $ e `div` d) in
--           addEquation eqn $ pure (newM, rest)
--   makeCount :: Either SymbolVar BoundVar -> Natural -> Count
--   makeCount (Left symbol) d = symbolVarCount symbol d
--   makeCount (Right bound) d = boundVarCount bound d
-- --if the LHS has symbolic vars, they must also appear on the RHS or the match will fail
-- matchCount (Count 0 as xs) (Count m bs ys)
--   = matchCount leftCount =<< maybeRightCount where
--     leftCount = Count 0 Empty xs
--     maybeRightCount = Count m <$> rightSymbolVarMap <*> pure ys
--     rightSymbolVarMap :: Equations (MMap SymbolVar (Sum Natural))
--     rightSymbolVarMap = matchSymbolVarMap (getSum <$> as) bs
--     matchSymbolVarMap :: MMap SymbolVar Natural -> MMap SymbolVar (Sum Natural) -> Equations (MMap SymbolVar (Sum Natural))
--     matchSymbolVarMap as bs = ifoldrM subtractSymbolVar bs as
--     subtractSymbolVar :: SymbolVar -> Natural -> MMap SymbolVar (Sum Natural) -> Equations (MMap SymbolVar (Sum Natural))
--     subtractSymbolVar var count m = case m ^. at var of
--       Nothing -> nothingES ""
--       Just (Sum occurs) -> case compare count occurs of
--         LT -> pure $ m & at var . _Just . _Wrapped' -~ count
--         EQ -> pure $ m & at var .~ Nothing
--         GT -> nothingES ""
-- --if the first count has a postive number, then we want to match it first
-- matchCount (Count n as xs) (Count m bs ys) = if n <= m
--   then matchCount (Count 0 as xs) (Count (m-n) bs ys)
--   else nothingES "matched a count with a bigger nat to a smaller nat"

matchInfCount :: Count -> InfCount -> Equations InfCount
--if you consume a finite number of symbols from an infinity, then an infinite number remain
matchInfCount (Count _ _ Empty) Infinity = pure Infinity
--if there is a "forall x" in the count, then morally you can think of it as consuming the infinite
--number of symbols - x can only really be set to any finite value, but eg, you can show the machine will
--consume 100 symbols, and 1000 symbols, etc, and so the machine must never stop consuming symbols
--however you leave the infinity on the tape for the next guy - if you need to consume 100 then 100
--symbols, or 1000 then 1 symbols, infinity will have your back
--note that adding an equation to send every variable to Infinity is a little bit aggressive
--if some of the vars are already set, this is fine, and we can ignore those - we want to send
--as many to infinity as possible though
--TODO:: Handle this better. Probably this is actually addEquation's job?
matchInfCount (Count _ _ xs) Infinity = addEquations (keys xs <&> (, Infinity)) $ pure Infinity
matchInfCount c (NotInfinity d) = NotInfinity <$> matchCount c d

finiteCount :: Natural -> Count
finiteCount n = Count n mempty mempty

finiteInfCount :: Natural -> InfCount
finiteInfCount = NotInfinity . finiteCount

symbolVarCount :: SymbolVar -> Natural -> Count
symbolVarCount a d = Count 0 (MonoidalMap (one (a, Sum d))) mempty

symbolVarInfCount :: SymbolVar -> Natural -> InfCount
symbolVarInfCount a d = NotInfinity $ symbolVarCount a d

boundVarCount :: BoundVar -> Natural -> Count
boundVarCount x d = Count 0 mempty (MonoidalMap (one (x, Sum d)))

boundVarInfCount :: BoundVar -> Natural -> InfCount
boundVarInfCount x d = NotInfinity $ boundVarCount x d

newBoundVar :: Int -> Count
newBoundVar n = Count 0 mempty $ MonoidalMap (one (BoundVar n, Sum 1))

newInfBoundVar :: Int -> InfCount
newInfBoundVar = NotInfinity . newBoundVar

--fails when the equation is inconsistent with what we already know
addEquationToMap :: (BoundVar, InfCount) -> Map BoundVar InfCount -> Either Text (Map BoundVar InfCount)
addEquationToMap (v, c) m = case m ^. at v of
  Nothing -> Right $ m & at v ?~ c
  --it's fine to assign the same count twice, but fails immediately if you assign
  --the same var to a new count. This is where we'd need to emit info to backtrack
  --if that ends up being a good feature to do
  Just c' -> unless (c == c') (Left "assigned to same var twice") >> Right m

addEquation :: (BoundVar, InfCount) -> Equations a -> Equations a
addEquation eqn (Equations (Right (m, a))) = case addEquationToMap eqn m of
  Left message -> Equations (Left message)
  (Right m') -> Equations (Right (m', a))
addEquation _eqn e@(Equations (Left _message)) = e

emitEquation :: BoundVar -> InfCount -> Equations ()
emitEquation l r = addEquation (l, r) $ pure ()

addEquations :: (Foldable t) => t (BoundVar, InfCount) -> Equations a -> Equations a
addEquations = appEndo . foldMap (Endo . addEquation)

mergeEqns :: Map BoundVar InfCount -> Map BoundVar InfCount -> Either Text (Map BoundVar InfCount)
mergeEqns = mergeA preserveMissing preserveMissing
  (zipWithAMatched (\k v1 v2 -> if v1 == v2 then Right v1
    else Left ("values failed to match: "
      <> show k <> " sent to " <> show v1 <> " and " <> show v2)))

newtype Equations a = Equations
  {runEquations :: Either Text (Map BoundVar InfCount, a)}
  deriving newtype (Eq, Ord, Show)

--Discard the message
getEquations :: Equations a -> Maybe a
getEquations = preview (_Right . _2) . runEquations

nothingES :: Text -> Equations a
nothingES text = Equations (Left text)

eitherES :: Either Text a -> Equations a
eitherES = Equations . fmap (Empty,)

instance Functor Equations where
  fmap f (Equations e) = Equations $ fmap (fmap f) e
instance Applicative Equations where
  pure s = Equations $ Right (Empty, s)
  (Equations f) <*> (Equations a) = Equations $ join $ mergeApp <$> f <*> a where
    mergeApp (eqns, f) (moreEqns, a) = (, f a) <$> mergeEqns eqns moreEqns

instance  Monad Equations where
  (Equations k) >>= f = Equations $ bind combine $ runEquations . f <$$> k
    where
    combine (eqns, Right (moreEqns, b))
      = (,b) <$> mergeEqns eqns moreEqns
    combine (_, l@(Left _message)) = l

instance MonadFail Equations where
  fail text = Equations $ Left $ fromString text

instance Filterable Equations where
  mapMaybe fm (Equations (Right (eqns, a))) = Equations $ (eqns,) <$> maybe (Left "wither") Right (fm a)
  mapMaybe _ (Equations (Left m)) = Equations $ Left m

updateCount :: Map BoundVar Count -> Count -> Count
updateCount m (Count n as xs) = Count n as Empty
  <> foldMap (updateVar m) (assocs xs) where
    updateVar :: Map BoundVar Count -> (BoundVar, Sum Natural) -> Count
    updateVar m (x, Sum n) = n `nTimes` getVar m x
    getVar :: Map BoundVar Count -> BoundVar -> Count
    getVar m x = case m^.at x of
      Just c -> c
      Nothing -> boundVarCount x 1

partiallyUpdateCount :: Map BoundVar InfCount -> Count -> Count
partiallyUpdateCount m (Count n as (MonoidalMap xs))
 = Count n as Empty <> foldMap (updateVar m) (M.assocs xs) where
  updateVar m (x, Sum n) = case m ^. at x of
    Nothing -> Count 0 Empty (MonoidalMap $ one (x, Sum n))
    Just (NotInfinity c) -> n `nTimes` c
    --TODO: what do we do here?
    Just Infinity -> error "infinity in partialupdate"

updateCountToInf :: Map BoundVar InfCount -> Count -> InfCount
updateCountToInf m (Count n as (MonoidalMap xs))
  = NotInfinity (Count n as Empty) <> foldMap (updateVar m) (M.assocs xs) where
  updateVar :: Map BoundVar InfCount -> (BoundVar, Sum Natural) -> InfCount
  updateVar m (x, Sum n) = n `nTimes` getVar m x
  getVar :: Map BoundVar InfCount -> BoundVar -> InfCount
  getVar m x = case m^.at x of
    Just c -> c
    Nothing -> error $ show m <> "\n" <> show x
      <> " a bound var wasn't mapped"
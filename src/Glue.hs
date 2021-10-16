module Glue where
import Relude
import Relude.Extra (bimapBoth)
import Control.Monad.Error.Class
import Control.Lens
import qualified Data.Map.Strict as M (assocs)
import Data.Map.Monoidal (deleteFindMin, singleton, assocs, MonoidalMap (MonoidalMap), intersectionWith, unionWith)

import Util
import Count
import Skip hiding (HeadMatch(..))
import ExpTape
import Turing



{-
Things to do: 
 --- skips that skip infinitely detector
 --- glue two skips together plan
 - heuristics for things around gluing making induction hypotheses 
 - i n d u c t i o n   m a c h i n e
-}

-- given a divisor d, a natural n and a map containing naturals m, either succeed at evenly dividing 
-- the distinguised natural and all the naturals in the map by the divisor, or fail
divStatics :: Natural -> Natural -> MMap k (Sum Natural) -> Maybe (Natural, MMap k (Sum Natural)) 
divStatics d n m = (,) <$> (n `maybeDiv` d) <*> (m `divMap` d) 


--given two counts, either produces the most general count that encompasses both of them or fails 
--probably this should be an Equations and that monad should be upgraded to have a spawn new var field
glueCounts :: Count -> Count -> Equations Count --Either Text (Count) 
glueCounts c d = case likeTerms c d of 
  --this is the two zerovar case, in which case all terms must be alike 
  (likes, Empty, Empty) -> pure likes
  --if one side has a var, it unifies if the other side's leftovers are divisible by that coefficient
  (_likes, OneVar 0 Empty k x, ZeroVar m bs) -> case divStatics k m bs of 
    Nothing -> fail "one/zero var failed to divide"
    Just (m', bs') -> do 
      emitEquation x $ NotInfinity $ ZeroVar m' bs'
      pure d 
  --pops to the above case
  (_likes, ZeroVar _ _, OneVar _ _ _ _) -> glueCounts d c
  --both sides leftovers must be divisible by the other var, in which case you add together the 
  --leftovers and make a new var that is the LCM of the two coefficents
  --TODO :: this function currently doesn't know how to create a new var
  (likes, OneVar n as k x, OneVar m bs j y) -> 
    case bisequence (divStatics k m bs, divStatics j n as) of 
      Nothing -> fail "one/one failed to divide"
      Just ((m', bs'), (n', as')) -> do 
        emitEquation x $ NotInfinity $ ZeroVar m' bs' 
        emitEquation y $ NotInfinity $ ZeroVar n' as'
        pure $ likes <> ZeroVar n as <> ZeroVar m bs 
           <> OneVar 0 Empty (lcm j k) undefined --this needs to be a new variable
  -- TODO :: emit a warning here?
  _ -> fail "one side had more than one var" 

--returns the part of the longer list that is not matched up via zip, 
--ie returns the longer list with the first (length shortlist) elements dropped 
remainingLonger :: [a] -> [b] -> Either [a] [b]
remainingLonger xs ys = if length xs < length ys
  then Right (drop (length xs) ys) 
  else Left (drop (length ys) xs)

--takes two lists, fails if they are incompatible, else returns a Left if some 
--of the first list was leftover, or a Right if 
--some of the second list was leftover 
glueTapeHalves :: forall s. (Eq s) => [(s, Count)] -> [(s, Count)] -> Equations (Leftover s)
glueTapeHalves xs ys = matched >> pure answer where
  zipped = zip xs ys --discards longer 
  matchOne :: ((s, Count), (s, Count)) -> Equations (s, Count)
  matchOne ((s, c), (t, d)) = do 
    -- TODO :: this works / makes sense as long as we never spawn any new variables, otherwise
    --  this really needs to be returning the new list as a result, which is built out of the
    --  thing unified from c and d 
    newCount <- glueCounts c d 
    if s == t then pure (s, newCount) else fail "matched tapes with different bits"
  matched :: Equations [(s, Count)]
  matched = traverse matchOne zipped 
  --if the start one is longer, it means we need to add to the *end*
  --if the end one is longer, we need to add to the start
  answer :: Leftover s
  answer = case remainingLonger xs ys of 
    Left xs -> End xs 
    Right ys -> Start ys

--things you add to the left and right of a Config or SkipEnd
data Tails s = Tails [(s, Count)] [(s, Count)] deriving (Eq, Ord, Show)

--whether you add the list to the start of the skip or you add it to the end of the skip
data Leftover s = Start [(s, Count)] | End [(s, Count)] deriving (Eq, Ord, Show)

leftoverTails :: (Leftover s, Leftover s) -> (Tails s, Tails s) 
leftoverTails (ls, rs) 
  = (Tails (getStart ls) (getStart rs), Tails (getEnd ls) (getEnd rs)) 
    where
      getStart (Start xs) = xs 
      getStart (End _) = [] 
      getEnd (Start _) = [] 
      getEnd (End xs) = xs 

applyTailsConfig :: (Eq s) => Tails s -> Config s -> Config s
applyTailsConfig (Tails lTail rTail) (Config p ls point rs) 
  = Config p (ls `etApp` lTail) point (rs `etApp` rTail)

applyTailsSkipEnd :: (Eq s) => Tails s -> SkipEnd s -> SkipEnd s 
applyTailsSkipEnd tails (EndMiddle c) = EndMiddle (applyTailsConfig tails c)
applyTailsSkipEnd (Tails lTail rTail) (EndSide p L rs) = case lTail of 
  [] -> EndSide p L (rs `etApp` rTail) 
  ((s, One) : remLTail) -> EndMiddle (Config p remLTail s (rs `etApp` rTail))
  ((s, c) : remLTail) -> 
    EndMiddle (Config p ((s, unsafeSubNatFromCount c 1) :remLTail) s (rs `etApp` rTail))
applyTailsSkipEnd (Tails lTail rTail) (EndSide p R ls) = case rTail of 
  [] -> EndSide p R (ls `etApp` lTail) 
  ((s, One) : remRTail) -> EndMiddle (Config p (ls `etApp` lTail) s remRTail)
  ((s, c) : remRTail) -> 
    EndMiddle (Config p (ls `etApp` lTail) s ((s, unsafeSubNatFromCount c 1) : remRTail))

--the leftovers on the left and right sides respectively
glueEndToBeginning :: (Eq s) => SkipEnd s -> Config s -> Equations (Leftover s, Leftover s)
glueEndToBeginning (EndMiddle (Config p ls s rs)) (Config q ls' s' rs') = do 
  if p == q then pure () else fail "phases were different"
  if s == s' then pure () else fail "points were different"
  lsLeftovers <- glueTapeHalves ls ls' 
  rsLeftovers <- glueTapeHalves rs rs'
  pure (lsLeftovers, rsLeftovers)
glueEndToBeginning (EndSide p L rs) (Config q ls' s' rs') = do 
  if p == q then pure () else fail "phases were different"
  (,) <$> pure (Start ((s', finiteCount 1) : ls')) <*> glueTapeHalves rs rs'
glueEndToBeginning (EndSide p R ls) (Config q ls' s' rs') = do
  if p == q then pure () else fail "phases were different" 
  (,) <$> glueTapeHalves ls ls' <*> pure (Start ((s', finiteCount 1) : rs'))

updateCount :: Map BoundVar Count -> Count -> Count 
updateCount m (Count n as xs) = Count n as Empty 
  <> foldMap (updateVar m) (assocs xs) where 
    updateVar :: Map BoundVar Count -> (BoundVar, Sum Natural) -> Count 
    updateVar m (x, Sum n) = n `nTimes` getVar m x 
    getVar :: Map BoundVar Count -> BoundVar -> Count 
    getVar m x = case m^.at x of 
      Just c -> c 
      Nothing -> boundVarCount x 1

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

updateConfig :: Map BoundVar Count -> Config s -> Config s 
updateConfig map (Config p ls point rs) = Config p (updateCount map <$$> ls) point (updateCount map <$$> rs) 

updateSkipEnd :: Map BoundVar Count -> SkipEnd s -> SkipEnd s 
updateSkipEnd map = \case 
  EndSide p d xs -> EndSide p d $ updateCount map <$$> xs --the problem is update count turns a count into an infcount but that doesn't work here
  EndMiddle config -> EndMiddle $ updateConfig map config 

-- updateDisplacement :: Map BoundVar Count -> Displacement Count -> Displacement Count
-- updateDisplacement map = \case 
--   Zero -> Zero 
--   OneDir d c -> OneDir d $ updateCount map c 
--   BothDirs c c' -> BothDirs (updateCount map c) (updateCount map c')

updateSkip :: Map BoundVar Count -> Skip s -> Skip s 
updateSkip map (Skip config end hops halts disp) = Skip 
  (updateConfig map config) 
  (updateSkipEnd map end) 
  (updateCount map hops) 
  halts
  (updateCount map <$> disp)

simplifyInfDisplacement :: Displacement InfCount -> Displacement InfCount 
simplifyInfDisplacement = \case 
  BothDirs Infinity Infinity -> error "double infinity ??"
  --commented out because these feel weird and I kind of want to not commit to them 
  -- BothDirs Infinity _c -> OneDir L Infinity 
  -- BothDirs _c Infinity -> OneDir R Infinity 
  BothDirs (NotInfinity c) (NotInfinity d) -> NotInfinity <$> simplifyDisplacement (BothDirs c d)
  other -> other

simplifyDisplacement :: Displacement Count -> Displacement Count
simplifyDisplacement d | traceShow d False = undefined
simplifyDisplacement Zero = Zero 
simplifyDisplacement (OneDir d c) = OneDir d c 
simplifyDisplacement (BothDirs c c') = case (c, c') of 
  (Empty, ans) -> OneDir R ans 
  (ans, Empty) -> OneDir L ans 
  -- TODO:: I'm pretty sure this code is redundant, make actually sure
  -- (Count n as xs, FinCount m) -> if n >= m 
  --   then OneDir L $ Count (n - m) as xs 
  --   else BothDirs (Count 0 as xs) (FinCount $ m - n)
  -- (FinCount n, Count m as xs) -> if m >= n
  --   then OneDir R $ Count (m - n) as xs 
  --   else BothDirs (FinCount $ m - n) (Count 0 as xs)
  (Count n as xs, Count m bs ys) -> let 
    (n', m') = subMin n m 
    (as', bs') = removeCommon' as bs 
    (xs', ys') = removeCommon' xs ys 
    in simplifyDisplacement $ BothDirs (Count n' as' xs') (Count m' bs' ys')
  where 
    subMin :: Natural -> Natural -> (Natural, Natural)
    subMin x y = (x - theMin, y - theMin) where 
      theMin = min x y 
    removeCommon' xs ys = bimapBoth (fmap Sum) $ removeCommon (getSum <$> xs) (getSum <$> ys) 
    --takes two maps and returns both, with the keys they both had subtracted out 
    removeCommon :: (Ord k) => MMap k Natural -> MMap k Natural -> (MMap k Natural, MMap k Natural)
    removeCommon xs ys = (unionWith (-) xs commonElts, unionWith (-) ys commonElts) where
      commonElts = intersectionWith min xs ys 
  

glueDisplacements :: Displacement Count -> Displacement Count -> Displacement Count
glueDisplacements Zero d = d 
glueDisplacements d Zero = d 
glueDisplacements (OneDir d c) (OneDir d' c') = if d == d' then OneDir d (c <> c') else case (c, c') of 
  (FinCount n, FinCount n') -> if n >= n' 
    then OneDir d $ FinCount $ n - n'
    else OneDir d' $ FinCount $ n' - n
  (_, _) -> case (d, d') of 
    (L, R) -> BothDirs c c'
    (R, L) -> BothDirs c' c 
    _ -> error "unreachable"
glueDisplacements (OneDir d c) (BothDirs lC rC) = case d of 
  L -> BothDirs (lC <> c) rC 
  R -> BothDirs lC (rC <> c) 
glueDisplacements both@(BothDirs _ _) one@(OneDir _ _) = glueDisplacements one both 
glueDisplacements (BothDirs lC rC) (BothDirs lC' rC') = BothDirs (lC <> lC') (rC <> rC')


--takes a first and a second skip and returns, if it is possible, a skip that
--results from applying one then the next. Tries to keep universals as general as
--possible but this is not guaranteed to find the most general universal quantifiers
glueSkips :: forall s. (Eq s, Show s) => Skip s -> Skip s -> Either Text (Skip s)
glueSkips (Skip startConfig middleSkipEnd c b d) (Skip middleConfig endSkipEnd c' b' d') 
 = uncurry updateSkip <$> munge (runEquations skipWithEquations) & _Right . displacement %~ simplifyDisplacement where
  munge :: Either Text (Map BoundVar InfCount, a) -> Either Text (Map BoundVar Count, a)
  munge = second $ first $ fmap unsafeDeInf
  unsafeDeInf :: InfCount -> Count 
  unsafeDeInf = \case 
    NotInfinity c -> c 
    Infinity -> error "unsafeDeInf" 
  skipWithEquations :: Equations (Skip s)
  skipWithEquations = do 
    if not b then pure () else fail "first skip halted"
    leftovers <- glueEndToBeginning middleSkipEnd middleConfig 
    let (startTails, endTails) = leftoverTails leftovers
    --trace ("start tails were\n" <> show startTails <> "\n" <> "end tails were\n" <> show endTails) $
    pure $ Skip (applyTailsConfig startTails startConfig) 
                (applyTailsSkipEnd endTails endSkipEnd) 
                (c <> c') 
                b'
                (glueDisplacements d d') 
              
skipGoesForever :: forall s. (Eq s, Show s) => Skip s -> Bool 
skipGoesForever skip = has _Right (glueSkips skip skip) 

glueMany :: (Eq s, Show s) => NonEmpty (Skip s) -> Either Text (Skip s)
glueMany (h :| tail) = foldlM glueSkips h tail 
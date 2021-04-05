module Glue where

import Relude
import Control.Monad.Error.Class
import Control.Lens
import Control.Unification
import Control.Unification.Types (UFailure(..))
import Data.Functor.Fixedpoint
import Data.Map.Monoidal (deleteFindMin, singleton, assocs)

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

divStatics :: Natural -> Natural -> MMap k (Sum Natural) -> Maybe (Natural, MMap k (Sum Natural)) 
divStatics d n m = (,) <$> (n `maybeDiv` d) <*> (m `divMap` d) 


--given two counts, either produces the most general count that encompasses both of them or fails 
--probably this should be an Equations and that monad should be upgraded to have a spawn new var field
glueCounts :: Count -> Count -> Either Text Count 
glueCounts c d = case likeTerms c d of 
  --this is the two zerovar case, in which case all terms must be alike 
  (likes, Empty, Empty) -> pure likes
  --if one side has a var, it unifies if the other side's leftovers are divisible by that coefficient
  (_likes, OneVar 0 Empty k _x, ZeroVar m bs) -> 
    maybe (Left "one/zero var failed to divide") Right $ divStatics k m bs >> pure d
  --pops to the above case
  (_likes, ZeroVar _ _, OneVar _ _ _ _) -> glueCounts d c
  --both sides leftovers must be divisible by the other var, in which case you add together the 
  --leftovers and make a new var that is the LCM of the two coefficents
  --TODO :: this function currently doesn't know how to create a new var
  (likes, OneVar n as k x, OneVar m bs j y) -> maybe (Left "one/one failed to divide") Right $ 
    divStatics k m bs >> divStatics j n as >> 
    pure (likes <> ZeroVar n as <> ZeroVar m bs <> OneVar 0 Empty (lcm j k) undefined)
  -- TODO :: emit a warning here?
  _ -> Left "one side had more than one var" 

--returns the part of the longer list that is not matched up via zip, 
--ie returns the longer list with the first (length shortlist) elements dropped 
remainingLonger :: [a] -> [b] -> Either [a] [b]
remainingLonger xs ys = if (length xs < length ys) 
  then Right (drop (length xs) ys) 
  else Left (drop (length ys) xs)

--takes two lists, fails if they are incompatible, else returns a Left if some 
--of the first list was leftover, or a Right if 
--some of the second list was leftover 
glueTapeHalves :: forall s. (Eq s) => [(s, Count)] -> [(s, Count)] -> Either Text (Leftover s)
glueTapeHalves xs ys = matched >> pure answer where
  zipped = (zip xs ys) --discards longer 
  matchOne :: ((s, Count), (s, Count)) -> Either Text ()
  matchOne ((s, c), (t, d)) = do 
    glueCounts c d 
    if s == t then pure () else Left "matched tapes with different bits"
  matched :: Either Text ()
  matched = traverse_ matchOne zipped 
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
  = glomPointConfig $ Config p (ls `etApp` lTail) point (rs `etApp` rTail)

applyTailsSkipEnd :: (Eq s) => Tails s -> SkipEnd s -> SkipEnd s 
applyTailsSkipEnd tails (EndMiddle c) = EndMiddle (applyTailsConfig tails c)

applyTailsSkipEnd (Tails [] rTail) (EndSide p L rs) = EndSide p L (rs `etApp` rTail) 
applyTailsSkipEnd (Tails ((s, c) : lTail) rTail) (EndSide p L rs) 
  = EndMiddle (Config p lTail (s, makeLoc c R) (rs `etApp` rTail))

applyTailsSkipEnd (Tails lTail []) (EndSide p R ls) = EndSide p R (ls `etApp` lTail) 
applyTailsSkipEnd (Tails lTail ((s, c) : rTail)) (EndSide p R ls)
  = EndMiddle (Config p (ls `etApp` lTail) (s, makeLoc c L) rTail)
{- 
nothingLeft :: Leftover s
nothingLeft = Start []
 -}
select :: Dir -> (a, a) -> a 
select d (l, r) = case d of 
  L -> l 
  R -> r 

--the leftovers on the left and right sides respectively
glueEndToBeginning :: (Eq s) => (SkipEnd s) -> Config s -> Either Text (Leftover s, Leftover s)
glueEndToBeginning (EndMiddle (Config p ls (s, loc) rs)) (Config q ls' (s', loc') rs') = do 
  if p == q then Right () else Left "phases were different"
  if s == s' then Right () else Left "points were different"
  case (loc, loc') of 
    (One, One) -> glueRest
    (Side c d, Side c' d') -> do
      if d == d' then Right () else Left ""
      glueCounts c c'
      glueRest
    -- TODO: I think it's ok if locations of end and beginning are different
    (_, _) -> Left "locations of end and beginning were different"
    where 
      glueRest = (,) <$> glueTapeHalves ls ls' <*> glueTapeHalves rs rs'
glueEndToBeginning (EndSide p L rs) (Config q ls' (s', loc') rs') = do 
  if p == q then Right () else Left "phases were different"
  case loc' of 
    One -> (,) <$> pure (Start ((s', finiteCount 1) : ls')) <*> glueTapeHalves rs rs'
    Side c L -> do 
      c' <- maybe (Left "subnat side L") Right $ subNatFromCount c 1 
      (,) <$> pure (Start ((s', finiteCount 1) : ls')) <*> glueTapeHalves rs ((s', c') : rs')
    Side c R -> (,) <$> pure (Start ((s', c) : ls')) <*> glueTapeHalves rs rs'
glueEndToBeginning (EndSide p R ls) (Config q ls' (s', loc') rs') = do
  if p == q then Right () else Left "phases were different" 
  case loc' of 
    One -> (,) <$> glueTapeHalves ls ls' <*> pure (Start ((s', finiteCount 1) : rs'))
    Side c R -> do 
      c' <- maybe (Left "subnat side R") Right $ subNatFromCount c 1 
      (,) <$> glueTapeHalves ls ((s', c') : ls') <*> pure (Start ((s', finiteCount 1) : rs'))
    Side c L -> (,) <$> glueTapeHalves ls ls' <*> pure (Start ((s', c) : rs'))



--takes a first and a second skip and returns, if it is possible, a skip that
--results from applying one then the next. Tries to keep universals as general as
--possible but this is not guaranteed to find the most general universal quantifiers
glueSkips :: (Eq s, Show s) => Skip s -> Skip s -> Either Text (Skip s)
glueSkips (Skip startConfig middleSkipEnd c b) (Skip middleConfig endSkipEnd c' b') = do 
  if not b then Right () else Left "first skip halted"
  leftovers <- glueEndToBeginning middleSkipEnd middleConfig 
  let (startTails, endTails) = leftoverTails leftovers
  pure $ Skip (applyTailsConfig startTails startConfig) 
              (applyTailsSkipEnd endTails endSkipEnd) 
              (c <> c') 
              b'


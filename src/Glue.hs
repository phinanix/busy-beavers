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


{-
Things to do: 
 - change from using tapevars to using "at the end of the skip it boops left or right"
 - write applyskip given this 
 - test / use glueing stuff to write
 --- skips that skip infinitely detector
 --- glue two skips together plan
 - heuristics for things around gluing making induction hypotheses 
 - i n d u c t i o n   m a c h i n e
 
-}
divStatics :: Natural -> Natural -> MMap k (Sum Natural) -> Maybe (Natural, MMap k (Sum Natural)) 
divStatics d n m = (,) <$> (n `maybeDiv` d) <*> (m `divMap` d) 

--given two counts, either produces the most general count that encompasses both of them or fails 
--probably this should be an Equations and that monad should be upgraded to have a spawn new var field
glueCounts :: Count -> Count -> Maybe Count 
glueCounts c d = case likeTerms c d of 
  --this is the two zerovar case, in which case all terms must be alike 
  (likes, Empty, Empty) -> pure likes
  --if one side has a var, it unifies if the other side's leftovers are divisible by that coefficient
  (likes, OneVar 0 Empty k x, ZeroVar m bs) -> divStatics k m bs >> pure d
  --pops to the above case
  (likes, ZeroVar _ _, OneVar _ _ _ _) -> glueCounts d c
  --both sides leftovers must be divisible by the other var, in which case you add together the 
  --leftovers and make a new var that is the LCM of the two coefficents
  --TODO :: this function currently doesn't know how to create a new var
  (likes, OneVar n as k x, OneVar m bs j y) -> divStatics k m bs >> divStatics j n as >> 
    (pure $ likes <> ZeroVar n as <> ZeroVar m bs <> OneVar 0 Empty (lcm j k) undefined)
  -- TODO :: emit a warning here?
  _ -> Nothing 


-- data VarOrU s a = Symbol s deriving (Functor, Foldable, Traversable)

-- instance (Eq s) => Unifiable (VarOrU s) where
--   zipMatch (Symbol s) (Symbol t) = if s == t
--     then Just (Symbol s)
--     else Nothing

-- varOrToUnify :: (BindingMonad (VarOrU s) v m) => VarOr s -> m (UTerm (VarOrU s) v)
-- varOrToUnify = \case
--   NotVar s -> pure $ UTerm $ Symbol s
--   Var _v -> UVar <$> freeVar

-- varOrFromUnify :: (Variable v) => UTerm (VarOrU s) v -> VarOr s
-- varOrFromUnify (UVar v) = Var $ TapeVar $ getVarID v
-- varOrFromUnify (UTerm (Symbol s)) = NotVar s

-- type FreeVars = MMap SymbolVar (Sum Natural)

-- data CountAtom a = Natural | SymbolAtom SymbolVar | BoundAtom a
--   deriving (Functor, Foldable, Traversable)

-- --this should really be a map or something, since the CountAtoms are unique and we
-- --want to search for them, but CountU has to be traversable
-- --invariant: the list is sorted with a possible natural at the beginning, then a
-- --sorted list of symbolAtoms, then an unknown order list of boundatoms
-- data CountU a = CountU [(Natural, CountAtom a)] deriving (Functor, Foldable, Traversable)

-- -- countToUnify :: Count -> CountU IntVar
-- -- countToUnify (Count n as xs) = CountU $ naturalAtom ++ symbolAtoms ++ boundAtoms where
-- --   naturalAtom = if n == 0 then [] else [(n, Natural)]
-- --   --assocs returns the list sorted
-- --   symbolAtoms = (\(v, Sum n) -> (n, SymbolAtom v)) <$> (assocs as)
-- --   boundAtoms :: _
-- --   boundAtoms = (\(BoundVar x, Sum n) -> (n, BoundAtom $ intVar x)) <$> assocs xs



-- data UnifyResult a = PerfectU | FirstU a | SecondU a deriving (Eq, Ord, Show)

-- -- combineUnifyResults :: (Monoid m) => UnifyResult m -> UnifyResult m -> Maybe (UnifyResult m)
-- -- combineUnifyResults PerfectU r = Just r
-- -- combineUnifyResults r PerfectU = Just r
-- -- combineUnifyResults (FirstU r) (FirstU r') = Just (FirstU (r <> r'))
-- -- combineUnifyResults (SecondU r) (SecondU r') = Just (SecondU (r <> r'))
-- -- combineUnifyResults _ _ = Nothing
-- --
-- -- unifyNaturals :: Natural -> Natural -> UnifyResult Natural
-- -- unifyNaturals n m = case compare n m of
-- --   LT -> SecondU (m - n)
-- --   EQ -> PerfectU
-- --   GT -> FirstU (n - m)
-- --
-- -- unifyFreeVars :: FreeVars -> FreeVars -> Maybe (UnifyResult (FreeVars))
-- -- unifyFreeVars Empty Empty = Just PerfectU
-- -- unifyFreeVars Empty bs = Just $ SecondU bs
-- -- unifyFreeVars as Empty = Just $ FirstU as
-- -- unifyFreeVars (deleteFindMin -> ((v, n), as)) (deleteFindMin -> ((w, m), bs))
-- --   = if v /= w then error "assert that mins are equal" else
-- --     case compare n m of
-- --       LT -> combineUnifyResults (SecondU $ singleton v (m-n)) =<< unifyFreeVars as bs
-- --       EQ -> unifyFreeVars as bs
-- --       GT -> combineUnifyResults (FirstU $ singleton v (n-m)) =<< unifyFreeVars as bs

-- -- unifyCounts :: (BindingMonad CountU v m)
-- --   => CountU v -> CountU v -> m (UnifyResult Count)
-- -- unifyCounts (CountU m as xs) (CountU n bs ys) = let
-- --   uniNs = unifyNaturals m n
-- --   uniFrees = unifyFreeVars as bs
-- --   in
-- --   undefined

-- --suppose (x, T) unifies with (4, T) -- this is a perfect match and we learn x -> 4
-- --but it is a bit tricky because we could continue matching x against more stuff, since
-- --it's univerally quantified :V
-- --this complexity is a cost of the fact that skips no longer have the no-repeat-symbols
-- --invariant, which might be a mistake
-- data HeadUnify s = PerfectH | FirstH (VarOr s) Count | SecondH (VarOr s) Count
--   deriving (Eq, Ord, Show)

-- unifyTapeHeads :: (Eq s) => (VarOr s, Count) -> (VarOr s, Count)
--   -> Equations s (HeadUnify s)
-- unifyTapeHeads f s = undefined -- pure PerfectH

-- --tape from end of first and start of second skip, respectively
-- --returns the suffix that you'd have to add to the end of the first skip for second
-- --skip to apply
-- unifyTapes :: (Eq s) => [(VarOr s, Count)] -> [(VarOr s, Count)]
--   -> Equations s [(VarOr s, Count)]
-- unifyTapes ls rs = undefined

-- unifyPoints :: (Eq s) => (VarOr s, Location Count) -> (VarOr s, Location Count)
--   -> Equations s _
-- unifyPoints p1 p2 = undefined

-- --takes a first config and a second config and if possible produces the suffixes
-- --necessary to apply to the first config that result in the second config applying
-- unifyConfigs :: (Eq s) => Config s -> Config s
--   -> Equations s ([(VarOr s, Count)], [(VarOr s, Count)])
-- unifyConfigs c1 c2 = undefined

-- --takes a first and a second skip and returns, if it is possible, a skip that
-- --results from applying one then the next. Tries to keep universals as general as
-- --possible but this is not guaranteed to find the most general universal quantifiers
-- glueSkips :: (Eq s) => Skip s -> Skip s -> Maybe (Skip s)
-- glueSkips first second = undefined

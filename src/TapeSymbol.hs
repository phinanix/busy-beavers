module TapeSymbol where

import Relude
import Text.Show
import Control.Lens
import Prettyprinter
import Data.Typeable (cast, typeOf)
import Safe.Exact
import Data.Map.Monoidal (keysSet)
import Data.Map.Strict (assocs, unions)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Util
import Count
import Turing
import Skip
import Notation (dispTuring)
import Mystery
import Glue (Leftover (..), remainingLonger)



data SkipOrigin s = Initial --from an atomic transition of the machine 
                  | Glued (Skip Count s) (Skip Count s) --from gluing together the two skips in question in order
                  | GlueStepRange Steps Steps --gluing together all skips used in a given range of steps
                  | Induction (SkipBook s) Int --from stepping forward the given number of times, with the given skipbook
                  | InductionHypothesis
                  | ChainedFrom (Skip Count s)
                  deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (SkipOrigin s)

--the data type storing various proven skips associated with a machine
--the "Phase, s" is the Phase on start and the "s" that the point is made of
type SkipBook s = Map (Phase,  s) (Map (Skip Count s) (SkipOrigin s))


class (Ord s, Show s, Pretty s, Typeable s) => TapeSymbol s where
  blank :: s
  getPoint :: s -> Bit -- the thing under the machinehead at the point
  toBits :: s -> [Bit]
  fromBits :: [Bit] -> ([s], [Bit]) --the second list is the one remaining
  --given a turing machine, how do you create a list of skips sufficient to 
  --cover all possible situations
  initBook :: Turing -> SkipBook s
  --given an edge which has just been defined in a given turing machine, take the 
  --skipbook before that edge was defined and give me the skipbook after the edge
  --was defined 
  --the default implementation just uses initBook; and updateBook is just
  --giving the ability to provide something more optimized than that
  updateBook :: Edge -> Turing -> SkipBook s -> SkipBook s
  updateBook _e tm _oldBook = initBook tm


--the skip that results from the atomic transition given an edge leading to a
--transition of the specified Phase, Bit, Dir
oneStepSkip :: Edge -> Phase -> Bit -> Dir -> Skip Count Bit
oneStepSkip (p, b) q c d = Skip
  (Config p [] b [])
  (SkipStepped q (Side d [(c, finiteCount 1)]))
  (finiteCount 1)

--the skip that results from an atomic transition which transitions a phase to itself
--writing the given bit and dir
infiniteSkip :: Edge -> Bit -> Dir -> Skip Count Bit
infiniteSkip (p, b) c L = Skip
  -- (Config p [] (b, Side (newBoundVar 0) R) [])
  (Config p [(b, newBoundVar 0)] b [])
  -- the plus one is because there is x bits to our left plus one we are pointed to 
  (SkipStepped p (Side L [(c, One <> newBoundVar 0)]))
  (One <> newBoundVar 0)

infiniteSkip (p, b) c R = Skip
  -- (Config p [] (b, Side (newBoundVar 0) L) [])
  (Config p [] b [(b, newBoundVar 0)])
  (SkipStepped p (Side R [(c, One <> newBoundVar 0)]))
  (One <> newBoundVar 0)

initTransSkip :: Edge -> Trans -> Set (Skip Count Bit)
--we need to modify this skip so that it's halt question is true
--a halting machine is assumed to write True and go left 
--(and not change phase, but conceptually it is now in "haltphase")
initTransSkip (p, b) Halt = one $ Skip
  (Config p [] b [])
  (SkipHalt (Side L [(Bit True, finiteCount 1)]))
  (finiteCount 1)
initTransSkip e@(p, _b) (Step q c d) | p == q = fromList
  [ oneStepSkip e q c d
  , infiniteSkip e c d
  ]
initTransSkip e (Step q c d) = one $ oneStepSkip e q c d

addSkipToBook :: (Ord s) => Skip Count s -> SkipOrigin s -> SkipBook s -> SkipBook s
addSkipToBook skip origin = atE (skip^.start.cstate, skip^.start.c_point)
  . at skip ?~ origin

addInitialSkipToBook :: (Ord s) => Skip Count s -> SkipBook s -> SkipBook s
addInitialSkipToBook skip = addSkipToBook skip Initial

addMultipleToBook :: (Ord s) => [(Skip Count s, SkipOrigin s)] -> SkipBook s -> SkipBook s
addMultipleToBook xs book = foldr (uncurry addSkipToBook) book xs

initBookBit :: Turing -> SkipBook Bit
initBookBit (Turing _n trans) = appEndo (foldMap (Endo . addInitialSkipToBook) skips) Empty where
  skips = foldMap (uncurry initTransSkip) $ assocs trans

varNotUsedInSkip :: Skip Count s -> BoundVar
varNotUsedInSkip skip = case S.lookupMax allInts of
  Nothing -> BoundVar 0
  Just x -> BoundVar (x + 1)
  where
  allInts = S.map getBoundVar allUsedVars
  allUsedVars = bifoldMap countUsedVars (const mempty) skip
  countUsedVars (Count _n _as xs) = keysSet xs

{-
when given a side, it only works if xs is length 1, and the skip has the following shape
  >A< goes to B>|
in which case we change it to 
  >A< (A, x) goes to (B, x+1)>|
-}
chainArbitrary :: forall s. (Eq s, Pretty s) => Skip Count s -> Either Text (Skip Count s)
chainArbitrary skip@(Skip start end steps) = case end of
  SkipStepped endPh (Side dir [(c, One)]) -> case start of 
    (Config startPh [] b []) -> do 
      guardMsg (startPh == endPh) $ "phases not equal"
      case dir of 
        --TODO handle steps obviously
        R -> Right $ Skip 
          (Config startPh [] b [(b, boundVarCount newVar 1)]) 
          (SkipStepped startPh (Side R [(b, One <> boundVarCount newVar 1)])) 
          Empty 
        L -> Right $ Skip 
          (Config startPh [(b, boundVarCount newVar 1)] b []) 
          (SkipStepped startPh (Side L [(b, One <> boundVarCount newVar 1)])) 
          Empty  
    _ -> Left "startconfig was the wrong shape"
      where 
      newVar = varNotUsedInSkip skip
  SkipStepped ph (Middle et) -> do
    (newStart, newEnd) <- matchConfigs start $ etToConfig ph et
    let (endPh, endTape) = configToET newEnd
    pure (Skip newStart (SkipStepped endPh $ Middle endTape) Empty) --TODO handle steps obviously
  _ -> Left "wasn't middle or side w/1"
  where
  newVar :: BoundVar
  newVar = varNotUsedInSkip skip
  matchConfigs :: Config Count s -> Config Count s -> Either Text (Config Count s, Config Count s)
  matchConfigs c1@(Config ph ls p rs) c2@(Config ph2 xs q ys) = do
    let rom = showP c1 <> " " <> showP c2
    guardMsg (ph == ph2 && p == q) $ "phases or points not equal: " <> rom
    (newLs, newXs) <- matchLists ls xs
    (newRs, newYs) <- matchLists rs ys
    pure (Config ph newLs p newRs, Config ph newXs p newYs)
  matchLists :: [(s, Count)] -> [(s, Count)] -> Either Text ([(s, Count)], [(s, Count)])
  matchLists xs ys = do
    --maybeRes :: Either Text [((s, Count), (s, Count))]
    maybeRes <- traverse (uncurry matchPairs) (zip xs ys) --zip discards longer 
    let leftover = case remainingLonger xs ys of
          Left xs_left -> Start xs_left
          Right ys_left -> End ys_left
    applyLeftover (unzip maybeRes, leftover)
  applyLeftover :: (([(s, Count)], [(s, Count)]), Leftover s) -> Either Text ([(s, Count)], [(s, Count)])
  applyLeftover ((starts, ends), lo) = case lo of
    Start [] -> Right (starts, ends)
    End [] -> Right (starts, ends)
    Start [(s, FinCount n)] -> Right (starts ++ [(s, boundVarCount newVar n)], ends)
    End [(s, FinCount n)] -> Right (starts, ends ++ [(s, boundVarCount newVar n)])
    _ -> Left $ "leftover was not a single finite thing: " <> showP lo
  matchPairs :: (s, Count) -> (s, Count) -> Either Text ((s, Count), (s, Count))
  matchPairs (s, c) (t, d) = do
    guardMsg (s == t) "two bits didn't match"
    (c', d') <- matchCounts c d
    pure ((s, c'), (t, d'))
  --first one is start, second one is end
  matchCounts :: Count -> Count -> Either Text (Count, Count)
  matchCounts c d = let rom = showP c <> " and " <> showP d in -- "rest of message" 
    if c == d then Right (c,d) else case (c,d) of
      --if we have a pair of counts like (x + 2, x + 5), every trip through, we increase the output by 3 (increaseAmt)
      -- so the total increase is 3 * y, for a "newVar" y, and that is the output below. 
    (OneVar n as k x, OneVar m bs j y) -> do
      guardMsg (x == y) $ "vars didn't match: " <> rom
      guardMsg (k == 1 && j == 1) $ "vars weren't both 1: " <> rom
      increaseAmt <- failMsg "chaining didn't increase" $ subCountFromCount (ZeroVar m bs) (ZeroVar n as)
      case increaseAmt of
        (FinCount incNat) -> let base =  OneVar n as 1 x in Right (base, base <> boundVarCount newVar incNat)
        _ -> Left $ "amt of increase was not finite: " <> showP increaseAmt <> "\n" <> rom
    _ -> Left $ "couldn't match counts:" <> rom
    
addChainedToBook :: SkipBook Bit -> SkipBook Bit
addChainedToBook sb = addMultipleToBook newSkipAndOrigins sb where
  allSkips = M.keys =<< M.elems sb
  mbChained = chainArbitrary <$> allSkips
  makeMBskipOrigin = \case 
    (skipIn, Right newSkip) -> Just (newSkip, ChainedFrom skipIn)
    _ -> Nothing 
  newSkipAndOrigins = mapMaybe makeMBskipOrigin $ zipExact allSkips mbChained 

instance TapeSymbol Bit where
  blank = Bit False
  getPoint = id
  toBits x = [x]
  fromBits = (,[])
  initBook = initBookBit

showMT :: (forall x. Show x => Show (f x)) => Mystery TapeSymbol f -> String
showMT (Mystery f) = Text.Show.show f

instance (forall x. Show x => Show (f x)) => Show (Mystery TapeSymbol f) where
  show = showMT


instance Eq (Mystery TapeSymbol f) where
  (Mystery f) == (Mystery g) = case cast g of
    Nothing -> False
    (Just g') -> f == g'

instance Ord (Mystery TapeSymbol f) where
  compare (Mystery f) (Mystery g) = let
    f_type = typeOf f
    g_type = typeOf g
    in
    case cast g of
      Nothing -> case compare f_type g_type of
        LT -> LT
        GT -> GT
        EQ -> error "unreachable"
      Just g' -> compare f g'


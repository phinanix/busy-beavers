module TapeSymbol where 

import Relude
import Text.Show 
import Control.Lens
import Prettyprinter
import Data.Typeable (cast, typeOf)
import Data.Map.Strict (assocs, keysSet, unions)

import Util
import Config
import Count 
import Turing
import Tape
import HaltProof
import Skip
import ExpTape
import Notation (dispTuring)
import Mystery


data SkipOrigin s = Initial --from an atomic transition of the machine 
                  | Glued (Skip Count s) (Skip Count s) --from gluing together the two skips in question in order
                  | GlueStepRange Steps Steps --gluing together all skips used in a given range of steps
                  | Induction (SkipBook s) Int --from stepping forward the given number of times, with the given skipbook
                  | InductionHypothesis
                  deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (SkipOrigin s)

--the data type storing various proven skips associated with a machine
--the "Phase, s" is the Phase on start and the "s" that the point is made of
type SkipBook s = Map (Phase,  s) (Map (Skip Count s) (SkipOrigin s))


class (Ord s, Show s, Pretty s) => TapeSymbol s where
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


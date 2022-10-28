module Turing where

import Relude
import Relude.Unsafe as Unsafe (init, last)
import Relude.Extra.Bifunctor
import qualified Text.Show
import Control.Lens hiding ((<|), (.=))
import Control.Lens.Extras
import Data.List.NonEmpty ((<|))
import Prettyprinter
import qualified Data.Map as M
import Data.Aeson
--import Notation


--the Phase a turing machine is in, to not conflict with State
newtype Phase = Phase { unPhase :: Int} deriving (Eq, Ord, Generic)
instance ToJSON Phase where 
    toEncoding = genericToEncoding defaultOptions
instance FromJSON Phase where 
instance Show Phase where
  show (Phase i) = "(Phase " <> show i <> ")"

data Dir = L | R deriving (Eq, Ord, Show, Generic)
instance ToJSON Dir where 
    toEncoding = genericToEncoding defaultOptions
instance FromJSON Dir where 
newtype Bit = Bit Bool deriving (Eq, Ord, Show, Generic)
instance ToJSON Bit where 
  toEncoding = genericToEncoding defaultOptions
instance FromJSON Bit 
type Edge = (Phase, Bit)
data Trans = Halt | Step Phase Bit Dir deriving (Eq, Ord, Show, Generic)

--a Turing machine
data Turing = Turing
  { states :: Int --the number of states a machine has
  , transitions :: Map Edge Trans
  } deriving (Eq, Ord, Show, Generic)

instance NFData Bit
instance NFData Phase
instance NFData Dir
instance NFData Trans
instance NFData Turing

getPhase :: Trans -> Maybe Phase
getPhase Halt = Nothing
getPhase (Step p _ _) = Just p

mirrorDir :: Dir -> Dir
mirrorDir L = R
mirrorDir R = L

mirrorTrans :: Trans -> Trans
mirrorTrans Halt = Halt
mirrorTrans (Step p b d) = Step p b $ mirrorDir d

mirrorTuring :: Turing -> Turing
mirrorTuring (Turing stateCount transitions)
  = Turing stateCount $ mirrorTrans <$> transitions
--
uniDir :: NonEmpty Dir
uniDir = L :| [R]

uniBit :: NonEmpty Bit
uniBit = Bit False :| [Bit True]

dispBit :: Bit -> Text
dispBit (Bit False) = "F"
dispBit (Bit True) = "T"

instance Pretty Bit where
  pretty = pretty . dispBit

dispPhase :: Phase -> Text
dispPhase (Phase i) = show i

instance Pretty Phase where
  pretty = pretty . dispPhase

dispEdge :: Edge -> Text
dispEdge (p, b) = dispPhase p <> " " <> show b

dispTrans :: Trans -> Text
dispTrans Halt = "Halt"
dispTrans (Step p b d) = dispPhase p <> " " <> show b <> " " <> show d

dispET :: Edge -> Trans -> Text
dispET e t = dispEdge e <> " | " <> dispTrans t <> "\n"


--crashes if the Int is not >0, which is true of much of the program
uniPhase :: Int -> NonEmpty Phase
uniPhase n = Phase <$> 0 :| [1.. n-1]

uniEdge :: Int -> NonEmpty Edge
uniEdge n = do
  i <- uniPhase n
  bit <- uniBit
  pure (i, bit)

uniTrans :: Int -> NonEmpty Trans
uniTrans n = Halt :| toList (do
  i <- uniPhase n
  bit <- uniBit
  dir <- uniDir
  pure $ Step i bit dir)

--this is where it starts to become obvious universe is a typeclass
--but many of mine are parameterized on an Int and that sounds annoying to deal with
--this universe is made of maps that have all the given keys, each associated with
--every possible value
uniMap :: forall k v. Ord k => NonEmpty k -> NonEmpty v -> NonEmpty (Map k v)
uniMap ks vs = foldlM addKey Empty ks where
  addKey :: Map k v -> k -> NonEmpty (Map k v)
  addKey !m k = do
    v <- vs
    pure $ m & at k ?~ v

uniTuring :: Int -> NonEmpty Turing
uniTuring n = do
  let ks = uniEdge n
      vs = uniTrans n
  m <- uniMap ks vs
  pure $ Turing n m

type Steps = Int

-- low priority todo :: filter out the machines which have duplicate states
-- creates a list of the various Turing machines that could result from filling
-- in the specified unknown edge, reducing via symmetry - if there are multiple
-- unused states, only sends us to the lowest numbered one
-- does not check that the edge is unknown, a precondition of correctness
branchOnEdge :: Edge -> Turing -> [Turing]
branchOnEdge e@(Phase newPhase, _) (Turing n m) = --if elem bb3test out then (trace $ toString $ dispTuring (Turing n m)) out else
  out where
  out = filter (not . isSmallerMachine) candidates
  candidates = Turing n <$> addTrans <$> possibleTrans
  addTrans t = m & at e ?~ t
  --if we're assigned the last unknown transition, we have to halt
  possibleTrans = if length m == 2*n - 1 then one Halt else
    --we have to use every state at least once, so when the last unused state (n-1) is
    --being assigned, or it has already been, we have to consider (not require) halting
    if used (n-2) then Halt : continueTrans else continueTrans
  --we use nondeterminism to pick all possibilities
  continueTrans = toList $ do
    p <- validStates
    bit <- uniBit
    dir <- uniDir
    pure $ Step p bit dir
  validStates = if used (n-1)
    --all states are used, so all are valid
    then Phase <$> 0 :| [1..(n-1)]
    --some states are used, plus we can use the next unused state
    else Phase <$> (firstUnused <| usedStates)
  --this could go off the end, but is only used when the end isn't used
  firstUnused = 1 + view last1 usedStates
  --we assume 0 is used, since we don't deal with the empty machine
  --and the NonEmpty is nice
  usedStates = 0 :| filter used [1.. (n-1)]
  --a state is used if either transition is
  used i = is _Just (m ^. at (Phase i, Bit False))
        || is _Just (m ^. at (Phase i, Bit True))
        || i == newPhase
  equalJusts (Just a) (Just b) = a == b
  equalJusts _ _ = False
  equalStates m i j =
    (m ^. at (i, Bit False)) `equalJusts` (m ^. at (j, Bit False))
    &&
    (m ^. at (i, Bit True)) `equalJusts` (m ^. at (j, Bit True))
  isSmallerMachine (Turing s m) = any (uncurry (equalStates m)) $
    bimapBoth Phase <$> allpairs s
  --j can't equal i because that would produce (i,i), but of course state i is always the same as
  --state i and this does not disqualify a machine
  allpairs n = [(i,j) | i <- [0.. n-1], j <- [0.. i-1] ]

--the two "symmetry broken" machines that can be started with
--one only need use the "1" machine to prove the function that counts 1s, but
--either could lead to a steps champion
--not valid for n=1, where the machine must halt immediately, or run forever.
startMachine0 :: Int -> Turing
startMachine0 1 = uni1Machine
startMachine0 n = Turing n $ one ((Phase 0, Bit False), Step (Phase 1) (Bit False) R)
startMachine1 :: Int -> Turing
startMachine1 1 = uni1Machine
startMachine1 n = Turing n $ one ((Phase 0, Bit False), Step (Phase 1) (Bit True) R)
--for n=1 if you don't halt right away, you are doomed to loop forever
uni1Machine :: Turing
uni1Machine = Turing 1 $ one ((Phase 0, Bit False), Halt)

fillInMachine :: Turing -> Turing
fillInMachine = \case
  Turing n map -> Turing n (map `M.union` newMap)
    where
    relEdges = filter (`M.notMember` map) $ toList $ uniEdge n
    newMap = M.fromList $ (, Halt) <$> relEdges 
module Beaver where
import Control.Lens
import Relude hiding (state)
import Relude.Unsafe as Unsafe (init, last)
--the Phase a turing machine is in, to not conflict with State
newtype Phase = Phase { unPhase :: Int} deriving (Eq, Ord, Show, Generic)
data Dir = L | R deriving (Eq, Ord, Show, Generic)
type Bit = Bool
type Edge = (Phase, Bit)
data Trans = Halt | Step Phase Bit Dir deriving (Eq, Ord, Show, Generic)

--a Turing machine
data Turing = Turing
  { states :: Int --the number of states a machine has
  , transitions :: Map Edge Trans
  } deriving (Eq, Ord, Show, Generic)

instance NFData Phase
instance NFData Dir
instance NFData Trans
instance NFData Turing

mirrorDir :: Dir -> Dir
mirrorDir L = R
mirrorDir R = L

mirrorTrans :: Trans -> Trans
mirrorTrans Halt = Halt
mirrorTrans (Step p b d) = Step p b $ mirrorDir d

mirrorTuring :: Turing -> Turing
mirrorTuring (Turing stateCount transitions)
  = Turing stateCount $ mirrorTrans <$> transitions where

uniDir :: NonEmpty Dir
uniDir = L :| [R]

uniBit :: NonEmpty Bit
uniBit = False :| [True]

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
uniMap ks vs = foldlM (addKey) Empty ks where
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

data Tape = Tape
  { left :: [Bit]
  , point :: Bit
  , right :: [Bit]
  } deriving (Eq, Ord, Show, Generic)
instance NFData Tape


--TODO:: modify this so that it never accumulates zeros where it should not
--functions to move the point of the zipper left and right
--returning nothing if the list ends
tapeLeft :: Tape -> Tape
--when we'd stack an false bit onto the implicitly infinite stack of False,
--drop it instead
tapeLeft (Tape [] False []) = Tape [] False []
tapeLeft (Tape (l : ls) False []) = Tape ls l []
tapeLeft (Tape [] h rs) = Tape [] False (h : rs)
tapeLeft (Tape (l : ls) h rs) = Tape ls l (h : rs)

tapeRight :: Tape -> Tape
--analagous to above
tapeRight (Tape [] False []) = Tape [] False []
tapeRight (Tape [] False (r : rs)) = Tape [] r rs
tapeRight (Tape ls h []) = Tape (h : ls) False []
tapeRight (Tape ls h (r : rs)) = Tape (h : ls) r rs

mirrorTape :: Tape -> Tape
mirrorTape (Tape ls h rs) =  Tape rs h ls

ones :: Tape -> Int
ones (Tape ls h rs) = length $ filter (==True) $ ls <> rs <> [h]

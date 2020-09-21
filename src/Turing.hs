module Turing where
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
  = Turing stateCount $ mirrorTrans <$> transitions where
--
uniDir :: NonEmpty Dir
uniDir = L :| [R]

uniBit :: NonEmpty Bit
uniBit = False :| [True]

dispBit :: Bit -> Text
dispBit False = "0"
dispBit True = "1"

dispPhase :: Phase -> Text
dispPhase (Phase i) = show i

dispEdge :: Edge -> Text
dispEdge (p, b) = dispPhase p <> " " <> show b

dispTrans :: Trans -> Text
dispTrans Halt = "Halt"
dispTrans (Step p b d) = dispPhase p <> " " <> show b <> " " <> show d

dispET :: Edge -> Trans -> Text
dispET e t = dispEdge e <> " | " <> dispTrans t <> "\n"

dispTuring :: Turing -> Text
dispTuring (Turing _ transitions) = ifoldMap dispET transitions

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

type Steps = Int

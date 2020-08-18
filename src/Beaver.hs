module Beaver where
import Control.Lens
import Relude
import qualified Relude.Unsafe as Unsafe hiding (at)

--the Phase a turing machine is in, to not conflict with State
data Phase = Halt | Phase Int deriving (Eq, Ord, Show)
data Dir = L | R deriving (Eq, Ord, Show)
type Bit = Bool
type Edge = (Int, Bit)
type Trans = (Phase, Bit, Dir)
--TODO :: Define a type edge, that is just an Int and a Bool, the two things read from the tape,
-- and modify the enumeration function so that it does not put Halt in the transition map

--TODO :: look up ways to enumerate finite types and compare to this, it might be a good way to enumerate things

--a Turing machine
data Turing = Turing
  { states :: Int --the number of states a machine has
  , transitions :: Map Edge Trans
  } deriving (Eq, Ord, Show)

data Zipper a = Zipper
  { left :: [a]
  , point :: a
  , right :: [a]
  }

--functions to move the point of the zipper left and right
--returning nothing if the list ends
zipLeft :: Zipper a -> Maybe (Zipper a)
zipLeft (Zipper [] _ _) = Nothing
zipLeft (Zipper (x : xs) point right) = Just $ Zipper xs x (point : right)

zipRight :: Zipper a -> Maybe (Zipper a)
zipRight (Zipper _ _ []) = Nothing
zipRight (Zipper left point (x : xs)) = Just $ Zipper (point : left) x xs

type Tape = Zipper Bit
type SimState = (Int, Tape)

initState :: SimState
initState = (0, Zipper (repeat False) False (repeat False))

--returns right if simulation was successful
--returns left and the unknown edge if we don't know how to make progress
--from the current state, because it isn't in the transition map, or
--returns only the final tape if the machine halts, or returns the new state
simStep :: Turing -> SimState -> Either Edge (Either Tape SimState)
simStep (Turing _ trans ) (i, (Zipper l bit r))
  = case trans ^. at (i, bit) of
      Nothing -> Left (i, bit)
      --these fromJusts are safe because the tape is infinite
      Just (Halt, newBit, L) ->
        Right $ Left $ Unsafe.fromJust $ zipLeft $ Zipper l newBit r
      Just (Halt, newBit, R) ->
        Right $ Left $ Unsafe.fromJust $ zipRight $ Zipper l newBit r
      Just (Phase j, newBit, L) ->
        Right $ Right $ (j, Unsafe.fromJust $ zipLeft $ Zipper l newBit r)
      Just (Phase j, newBit, R) ->
        Right $ Right $ (j, Unsafe.fromJust $ zipRight $ Zipper l newBit r)

--

uniDir :: NonEmpty Dir
uniDir = L :| [R]

uniBit :: NonEmpty Bit
uniBit = False :| [True]

--crashes if the Int is not >0, which is true of much of the program
uniFin :: Int -> NonEmpty Int
uniFin n = 0 :| [1.. n-1]

uniPhase :: Int -> NonEmpty Phase
uniPhase n = Halt :| toList (Phase <$> uniFin n)

uniEdge :: Int -> NonEmpty Edge
uniEdge n = do
  i <- uniFin n
  bit <- uniBit
  pure (i, bit)

uniTrans :: Int -> NonEmpty Trans
uniTrans n = do
  phase <- uniPhase n
  bit <- uniBit
  dir <- uniDir
  pure (phase, bit, dir)

--this is where it starts to become obvious universe is a typeclass
--but many of mine are parameterized on an Int and that sounds annoying to deal with
--this universe is made of maps that have all the given keys, each associated with
--every possible value
uniMap :: forall k v. Ord k => NonEmpty k -> NonEmpty v -> NonEmpty (Map k v)
uniMap ks vs = foldlM addKey Empty ks where
  addKey :: Map k v -> k -> NonEmpty (Map k v)
  addKey m k = do
    v <- vs
    pure $ m & at k ?~ v

uniTuring :: Int -> NonEmpty Turing
uniTuring n = do
  let ks = uniEdge n
      vs = uniTrans n
  m <- uniMap ks vs
  pure $ Turing n m

uni3size :: Int
uni3size = length $ uniTuring 3

uni4size :: Int
uni4size = length $ uniTuring 4

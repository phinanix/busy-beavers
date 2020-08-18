module Beaver where
import Control.Lens
import Relude hiding (state)

--the Phase a turing machine is in, to not conflict with State
data Dir = L | R deriving (Eq, Ord, Show)
type Bit = Bool
type Edge = (Int, Bit)
data Trans = Halt | Step Int Bit Dir deriving (Eq, Ord, Show)
--TODO :: Define a type edge, that is just an Int and a Bool, the two things read from the tape,
-- and modify the enumeration function so that it does not put Halt in the transition map

--TODO :: look up ways to enumerate finite types and compare to this, it might be a good way to enumerate things

--a Turing machine
data Turing = Turing
  { states :: Int --the number of states a machine has
  , transitions :: Map Edge Trans
  } deriving (Eq, Ord, Show)


uniDir :: NonEmpty Dir
uniDir = L :| [R]

uniBit :: NonEmpty Bit
uniBit = False :| [True]

--crashes if the Int is not >0, which is true of much of the program
uniFin :: Int -> NonEmpty Int
uniFin n = 0 :| [1.. n-1]

uniEdge :: Int -> NonEmpty Edge
uniEdge n = do
  i <- uniFin n
  bit <- uniBit
  pure (i, bit)

uniTrans :: Int -> NonEmpty Trans
uniTrans n = Halt :| toList (do
  i <- uniFin n
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

data Tape = Tape
  { left :: [Bit]
  , head :: Bit
  , right :: [Bit]
  }

--functions to move the point of the zipper left and right
--returning nothing if the list ends
tapeLeft :: Tape -> Tape
tapeLeft (Tape [] h rs) = Tape [] False (h : rs)
tapeLeft (Tape (l : ls) h rs) = Tape ls l (h : rs)

tapeRight :: Tape -> Tape
tapeRight (Tape ls h []) = Tape (h : ls) False []
tapeRight (Tape ls h (r : rs)) = Tape (h : ls) r rs

dispTape :: Tape -> String
dispTape (Tape ls h rs) = show (reverse ls) <> "  [" <> show h <> "]  " <> show rs

type SimState = (Int, Tape)
dispSimState :: SimState -> String
dispSimState (i, tape) = "state: " <> show i <> " tape: " <> dispTape tape

--Unknown means we don't know how to make progress
--from the current state, because it isn't in the transition map
--Stop means the machine halted with the given tape
--Continue means the machien hasn't halted and the current state is given
data SimResult = Unknown Edge | Stop Tape | Continue SimState

initState :: SimState
initState = (0, Tape [] False [])

simStep :: Turing -> SimState -> SimResult
simStep (Turing _ trans ) (i, (Tape ls bit rs))
  = case trans ^. at (i, bit) of
    Nothing -> Unknown (i, bit)
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      Stop $ tapeLeft $ Tape ls True rs
    Just (Step j newBit L) ->
      Continue $ (j, tapeLeft $ Tape ls newBit rs)
    Just (Step j newBit R) ->
      Continue $ (j, tapeRight $ Tape ls newBit rs)

--simulates a machine for the given number of steps
simulate :: Int -> SimState -> Turing -> SimResult
simulate ( (\i -> i <= 0) -> True) state _ = Continue state
simulate steps state t = case simStep t state of
  result@(Unknown _) -> result
  result@(Stop _) -> result
  (Continue newState) -> simulate (steps - 1) newState t

dispResult :: SimResult -> String
dispResult (Unknown edge) = "Simulating got stuck on " <> show edge
dispResult (Stop tape) = "Simulating finished with the tape: " <> dispTape tape
dispResult (Continue state) = "Simulating didn't finish, we reached state: " <> dispSimState state

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
prevPhase :: Int -> Phase -> Phase
prevPhase n Halt = Phase (n-1)
prevPhase _ (Phase 0) = Halt
prevPhase _ (Phase k) = Phase (k-1)

nextPhase :: Int -> Phase -> Phase
nextPhase _ Halt = Phase 0
nextPhase n (Phase k) = if k == n-1 then Halt else Phase $ k+1

nextEdge :: Int -> Edge -> Edge
nextEdge _ (i, False) = (i, True)
nextEdge n (i, True) = (if i == n-1 then 0 else i+1, False)

prevEdge :: Int -> Edge -> Edge
prevEdge n (i, False) = (if i == 0 then n-1 else i-1, True)
prevEdge _ (i, True) = (i, False)

firstTrans :: Int -> Trans
firstTrans _ = (Halt, False, L)

lastTrans :: Int -> Trans
lastTrans n = (Phase (n-1), True, R)

nextTrans :: Int -> Trans -> Trans
nextTrans _ (phase, False, L) = (phase, False, R)
nextTrans _ (phase, False, R) = (phase, True, L)
nextTrans _ (phase, True, L) = (phase, True, R)
nextTrans n (phase, True, R) = (nextPhase n phase, False, L)

prevTrans :: Int -> Trans -> Trans
prevTrans n (phase, False, L) = (prevPhase n phase, True, R)
prevTrans _ (phase, False, R) = (phase, False, L)
prevTrans _ (phase, True, L) = (phase, False, R)
prevTrans _ (phase, True, R) = (phase, True, L)

edgeList :: Int -> [Edge]
edgeList n = ((,False) <$> [0.. n-1]) ++ ((,True) <$> [0.. n-1])

--the lexicographically first turing machine of a certain size
firstTM :: Int -> Turing
firstTM n = if n < 1 then error "TM must have at least one state" else
  Turing n $ fromList $ (\k -> (k, firstTrans n)) <$> edgeList n

lastTM :: Int -> Turing
lastTM n = if n < 1 then error "TM must have at least one state" else
  Turing n $ fromList $ (\k -> (k, lastTrans n)) <$> edgeList n

--returns "Nothing" exactly when called on lastTM
nextTM :: Turing -> Maybe Turing
nextTM t@(Turing n tMap) = if t == (lastTM n) then Nothing else
  Just $ Turing n $ nextTMap tMap where
  nextTMap :: Map Edge Trans -> Map Edge Trans
  nextTMap = nextAtEdge (n-1, True)
  nextAtEdge :: Edge -> Map Edge Trans -> Map Edge Trans
  nextAtEdge edge m = case m ^. at edge of
    Just trans -> if trans == lastTrans n then
      --wrap around to first trans, and increment the next counter up
      nextAtEdge (prevEdge n edge) $ m & at edge ?~ firstTrans n else
      --just increment the current transition
      m & at edge ?~ nextTrans n trans
    Nothing -> error "nextTM is only defined on total turing machines"
universeTM :: Int  -> [Turing]
universeTM n = recurse $ Just $ firstTM n where
  --the list starting with t, going until the lastTM, or the empty list
  recurse :: Maybe Turing -> [Turing]
  recurse Nothing = []
  recurse (Just t) = t : recurse (nextTM t)

uni3size :: Int
uni3size = length $ universeTM 3

uni4size :: Int
uni4size = length $ universeTM 4

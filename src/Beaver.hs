module Beaver where
import Control.Lens
import Relude
import qualified Relude.Unsafe as Unsafe hiding (at)

--the Phase a turing machine is in, to not conflict with State
data Phase = Halt | Phase Int deriving (Eq, Ord, Show)
data Dir = L | R deriving (Eq, Ord, Show)
type Bit = Bool
type Trans = (Phase, Bit, Dir)

--a Turing machine
data Turing = Turing
  { states :: Int --the number of states a machine has
  , transitions :: Map (Phase, Bit) Trans
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
type SimState = (Phase, Tape)

initState :: SimState
initState = (Phase 0, Zipper (repeat False) False (repeat False))

--returns right if simulation was successful
--returns left and the unknown phase if we don't know how to make progress
--from the current state, because it isn't in the transition map
--which for a well-formed TM is always true of the Halt state
simStep :: Turing -> SimState -> Either (Phase, Bit) SimState
simStep _ (Halt, Zipper _ bit _) =  Left (Halt, bit)
simStep (Turing _ trans ) (phase@(Phase _), (Zipper l bit r))
  = case trans ^. at (phase, bit) of
      Nothing -> Left (phase, bit)
      --these fromJusts are safe because the tape is infinite
      Just (newPhase, newBit, L) ->
        Right $ (newPhase, Unsafe.fromJust $ zipLeft $ Zipper l newBit r)
      Just (newPhase, newBit, R) ->
        Right $ (newPhase, Unsafe.fromJust $ zipRight $ Zipper l newBit r)

--
prevPhase :: Int -> Phase -> Phase
prevPhase n Halt = Phase (n-1)
prevPhase _ (Phase 0) = Halt
prevPhase _ (Phase k) = Phase (k-1)

nextPhase :: Int -> Phase -> Phase
nextPhase _ Halt = Phase 0
nextPhase n (Phase k) = if k == n-1 then Halt else Phase $ k+1

nextEdge :: Int -> (Phase, Bit) -> (Phase, Bit)
nextEdge _ (phase, False) = (phase, True)
nextEdge n (phase, True) = (nextPhase n phase, False)

prevEdge :: Int -> (Phase, Bit) -> (Phase, Bit)
prevEdge n (phase, False) = (prevPhase n phase, True)
prevEdge _ (phase, True) = (phase, False)

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

transList :: Int -> [(Phase, Bit)]
transList n = ((,False) <$> allPhases n) ++ ((,True) <$> allPhases n)

allPhases :: Int -> [Phase]
allPhases n = Halt : (Phase <$> [0.. n-1])

--the lexicographically first turing machine of a certain size
firstTM :: Int -> Turing
firstTM n = if n < 1 then error "TM must have at least one state" else
  Turing n $ fromList $ (\k -> (k, firstTrans n)) <$> transList n

lastTM :: Int -> Turing
lastTM n = if n < 1 then error "TM must have at least one state" else
  Turing n $ fromList $ (\k -> (k, lastTrans n)) <$> transList n

--returns "Nothing" exactly when called on lastTM
nextTM :: Turing -> Maybe Turing
nextTM t@(Turing n tMap) = if t == (lastTM n) then Nothing else
  Just $ Turing n $ nextTMap tMap where
  nextTMap :: Map (Phase, Bit) Trans -> Map (Phase, Bit) Trans
  nextTMap = nextAtTrans (Phase (n-1), True)
  nextAtTrans :: (Phase, Bit) -> Map (Phase, Bit) Trans -> Map (Phase, Bit) Trans
  nextAtTrans edge m = case m ^. at edge of
    Just trans -> if trans == lastTrans n then
      --wrap around to first trans, and increment the next counter up
      nextAtTrans (prevEdge n edge) $ m & at edge ?~ firstTrans n else
      --just increment the current transition
      m & at edge ?~ nextTrans n trans
    Nothing -> error "nextTM is only defined on total turing machines"
universeTM :: Int  -> [Turing]
universeTM n = recurse $ Just $ firstTM n where
  --the list starting with t, going until the lastTM, or the empty list
  recurse :: Maybe Turing -> [Turing]
  recurse Nothing = []
  recurse (Just t) = t : recurse (nextTM t)

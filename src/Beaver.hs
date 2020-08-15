module Beaver where
import Control.Lens
import Relude
import qualified Relude.Unsafe as Unsafe hiding (at)

--the Phase a turing machine is in, to not conflict with State
data Phase = Halt | Phase Int deriving (Eq, Ord, Show)
data Dir = L | R deriving (Eq, Show)
type Bit = Bool

--a Turing machine
data Turing = Turing
  { states :: Int --the number of states a machine has
  , transitions :: Map (Phase, Bit) (Phase, Bit, Dir)
  }

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

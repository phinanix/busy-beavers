module HaltProof where

import Relude
import Control.Lens
import Data.Semigroup (Min(..), getMin)
import qualified Data.List.NonEmpty as NE (filter)
import Data.Map.Monoidal (MonoidalMap(..), findMin, deleteMin, deleteFindMin)
import Data.Map.Strict (assocs)
import Prettyprinter

import Util
import Config
import Turing
import Tape
import Notation
import Data.Aeson

--the type of proofs that a TM will not halt
-- - HaltUnreachable means the Halt state is never transitioned to from the current state
--   and any states it transitions to
-- - Cycle means that the state reached after a number of steps and a greater number
--   of steps is identical
-- - OffToInfinityN means that after the given number of steps, the machine will
--   continue off in the given direction infinitely, in a short loop, which is checked
--   up to a specified bound N
-- - BackwardSearch means that assuming the machine halted and searching backward to
--   see what might have resulted in that reaches a contradiction
-- - SkippedToInfinity means that after the given number of steps, the given skip
--   matches and proves the machine will consume an infinite amount of tape
-- - LinRecur a b means the machine enters linrecurrence on step a and the length
--   of the recurrence is b (a and b are measured in rule-steps right now)

--TODO: I rather want to rework all of these to better be divided up among the different
--methods and contain more info and stuff
data HaltProof s
  = HaltUnreachable Phase
  | Cycle Steps Steps
  | OffToInfinityN Steps Dir
  | BackwardSearch
--commenting out for now to fix a cyclic dependency, may need to move some things around
  | SkippedToInfinity Steps --(Skip Count s)
  --(start, period, translate-distance)
  | LinRecur Steps Steps Steps 
  --the width of the near head plus the size of the explored tree
  | NearHeadAI Int Int 
  deriving (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)
instance (NFData s) => NFData (HaltProof s)

instance ToJSON (HaltProof s) where 
  toEncoding = genericToEncoding defaultOptions

mirrorHaltProof :: HaltProof s -> HaltProof s
mirrorHaltProof (OffToInfinityN s d) = OffToInfinityN s $ mirrorDir d
--mirrorHaltProof (OffToInfinitySimple s d) = OffToInfinitySimple s $ mirrorDir d
mirrorHaltProof h = h

dispHaltProof :: Pretty s => HaltProof s -> Doc ann
dispHaltProof (HaltUnreachable p) = prettyText $ "there is no path to halt from phase: " <> dispPhase p
dispHaltProof (Cycle start end) = prettyText $ "the machine cycled over " <> show (end - start)
  <> " steps starting at step " <> show start
dispHaltProof (OffToInfinityN steps dir) = prettyText $ "the machine will continue off to the "
  <> show dir <> " forever after " <> show steps <> " steps"
dispHaltProof BackwardSearch = prettyText "a backwards search implies the machine never halts"
dispHaltProof (SkippedToInfinity steps) = prettyText ("after " <> show steps
  <> " steps, the machine applies the following skip which proves nonhalting:\n  ")
  -- <> pretty skip

instance (Pretty s) => Pretty (HaltProof s) where 
  pretty = dispHaltProof 

--runs a backward search from each halting state to see if it can reach a contradiction
--if we show that all ways to halt don't have paths leading into them from valid tapes
--then the halt state will never be reached
--of course no such procedure can be complete, so we put a finite depth on the search and
--give up after a while
backwardSearch :: Turing -> Maybe (HaltProof s)
--backwardSearch (Turing n trans) | length trans < (n*2) - 1 = Nothing
backwardSearch m@(Turing n trans) = let 
  msg = machineToNotation m <> show ans 
  f = if length trans < (n*2) - 1 then traceShow msg else id 
  ans = recurse 0 $ fromList $ (, Min 0) <$> (initState <$> unusedEdges) 
 in 
  f ans
  where 
  unusedEdges :: [Edge]
  unusedEdges = NE.filter (\e -> let t = trans ^. at e in t == Nothing || t == Just Halt) $ uniEdge n
  initState :: Edge -> (Phase,Tape Bit)
  initState (p, b) = (p, Tape [] b [])
  loop :: Int -> ((Phase, Tape Bit), Int) -> MonoidalMap (Phase, Tape Bit) (Min Int) -> Maybe (HaltProof s)
  loop globalSteps _ _ | globalSteps > backwardSearchGlobalLimit = Nothing
  loop _ (_, localSteps) _ | localSteps > backwardSearchSingleLimit = Nothing
  loop globalSteps (tape, localSteps) rest
    = case fromList $ (,Min $ localSteps+1) <$> backSteps tape of
      Empty -> recurse globalSteps rest
      possibilities -> recurse (globalSteps + 1) (possibilities <> rest)
  recurse :: Int -> MonoidalMap (Phase,Tape Bit) (Min Int) -> Maybe (HaltProof s)
  recurse _globalSteps Empty = Just $ BackwardSearch
  recurse globalSteps (deleteFindMin -> (f, rest)) = loop globalSteps (second getMin f) rest

  --this is subtle: it doesn't account for getting to your current undefined transition
  --by taking another undefined transition, but you must be able to reach _some_ undefined transition
  --by taking only real transitions or you will stay taking defined transitions forever, thus never halting
  transList = assocs trans
  candidateTrans :: Phase -> [(Edge, Trans)]
  candidateTrans p = filter ((== Just p) . getPhase . snd) transList
  --given a tape, returns all tapes that could result in the given tape
  backSteps :: (Phase,Tape Bit) -> [(Phase,Tape Bit)]
  backSteps (p, t) = mapMaybe (backStep (p,t)) $ candidateTrans p

  --precondition: the phase given and the getPhase of the Trans are the same
  backStep :: (Phase,Tape Bit) -> (Edge,Trans) -> Maybe (Phase, Tape Bit)
  --if the trans makes us step left, we care about what is to the right
  backStep (_p, Tape ls point []) ((inP, inB), (Step _p' _outB L))
    = Just $ (inP, Tape (point:ls) inB [])
  backStep (_p, Tape ls point (r:rs)) ((inP, inB), (Step _p' outB L))
    = guard (r == outB) >> (Just (inP, Tape (point:ls) inB rs))
  --conversely if the trans makes us step right, we were previously on the left
  backStep (_p, Tape [] point rs) ((inP, inB), (Step _p' _outB R))
    = Just $ (inP, Tape [] inB (point:rs))
  backStep (_p, Tape (l:ls) point rs) ((inP, inB), (Step _p' outB R))
    = guard (l == outB) >> (Just (inP, Tape ls inB (point:rs)))
  backStep _ (_, Halt) = Nothing

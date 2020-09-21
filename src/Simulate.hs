module Simulate where

import Relude hiding (cycle, state)
import Relude.Extra.Bifunctor
import Control.Lens hiding ((<|))
import Control.Lens.Extras
import Data.List.NonEmpty ((<|))
import qualified Data.List.NonEmpty as NE (filter)
import Data.Map.Monoidal (MonoidalMap(..), findMin, deleteMin, deleteFindMin)
import Data.Semigroup (Min(..), getMin)
import Data.Map.Strict (assocs)
--import Data.Witherable

import Util
import Turing
import Tape
import ExpTape (ExpTape(..), glomPointLeft, glomPointRight, etApp)
import qualified ExpTape as E
import Skip

--Pieces: turing machines with unknown edges
-- a simulator that does the usual simulate forward, while branching on unknown edges, according to
-- certain symmetry
-- a more powerful infinity prover
-- a Results type and an aggregator that adds to the results

data TMState a = TMState { _phase :: Phase, _tape :: a} deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (TMState a)

initTMState :: TMState Tape
initTMState = TMState (Phase 0) (Tape [] False [])

initExpTMState :: s -> TMState (ExpTape s Int)
initExpTMState s = TMState (Phase 0) (ExpTape [] (s, 1, L) [])

data PartialStepResult a = Unknown Edge | Stopped Dir a | Stepped Dir (TMState a)

data SimState a = SimState
  --positive
  { _stepCount :: Int
  --(stepCount `div` 2) steps after initTMState
  , _slowState :: (TMState a)
  --stepCount steps after initTMState
  , _fastState :: (TMState a)
  } deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (SimState a)

initSimState :: SimState Tape
initSimState = SimState 0 initTMState initTMState

initExpSimState :: s -> SimState (ExpTape s Int)
initExpSimState s = SimState 0 (initExpTMState s) (initExpTMState s)

data SimResult a = Halted Steps a
               | Continue (SimState a)
               | ContinueForever HaltProof
               deriving (Eq, Ord, Show)

--the type of proofs that a TM will not halt
-- - HaltUnreachable means the Halt state is never transitioned to from the current state
--   and any states it transitions to
-- - Cycle means that the state reached after a number of steps and a greater number
--   of steps is identical
-- - OffToInfinitySimple means that after the given number of steps, the machine will
--   continue off in the given direction infintitely, never changing states
-- - OffToInfinityN means that after the given number of steps, the machine will
--   continue off in the given direction infinitely, in a short loop, which is checked
--   up to a specified bound N
data HaltProof
  = HaltUnreachable Phase
  | Cycle Steps Steps
  | OffToInfinityN Steps Dir
  | BackwardSearch
--  | SkipOffEnd (Skip Bit)
  deriving (Eq, Ord, Show, Generic)
instance NFData HaltProof

mirrorHaltProof :: HaltProof -> HaltProof
mirrorHaltProof (OffToInfinityN s d) = OffToInfinityN s $ mirrorDir d
--mirrorHaltProof (OffToInfinitySimple s d) = OffToInfinitySimple s $ mirrorDir d
mirrorHaltProof h = h

simStep :: Turing -> TMState Tape -> PartialStepResult Tape
simStep (Turing _ trans ) (TMState p (Tape ls bit rs))
  = case trans ^. at (p, bit) of
    Nothing -> Unknown (p,bit)
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      (Stopped L $ tapeLeft $ Tape ls True rs)
    Just (Step q newBit L) ->
      (Stepped L (TMState q $ tapeLeft $ Tape ls newBit rs))
    Just (Step q newBit R) ->
      (Stepped R (TMState q $ tapeRight $ Tape ls newBit rs))

--WARNING :: this function is probably messy and kind of bad
simExpStep :: Turing -> TMState (ExpTape Bit Int) -> PartialStepResult (ExpTape Bit Int)
simExpStep (Turing _ trans) (TMState p tape@(ExpTape ls (bit, num, headDir) rs))
  = case trans ^. at (p, bit) of
    Nothing -> Unknown (p, bit)
    Just Halt -> Stopped L $ E.modify L True tape
    --we can skip to the end of the block when the new phase is the same as the old phase,
    --plus the dir is opposite the original dir (if you're on the L and go R)
    --TODO :: notice if this tries to skip to the end of the world
    Just (Step newP newBit moveDir) -> if newP == p && moveDir /= headDir then
      --we're about to move off the point, in block terms, not bit terms, so the side on which the point is is irrelevant
      Stepped moveDir (TMState newP $ E.tapeMove moveDir $ ExpTape ls (newBit, num, error "unused") rs)
      else Stepped moveDir (TMState newP $ E.modify moveDir newBit tape)

--either we skipped ahead to a new Phase and Tape or we might've proved infinity
data SkipResult s c = Skipped Phase (ExpTape s c) | SkippedOffEnd (Skip s)

--returns nothing if the skip is inapplicable, else returns a new tape
--the fact that the type is bit is only used when running off the tape, but for now I don't want to
--generalize that out (also ExpTape would have to be generalized)
applySkip :: Skip Bit -> (Phase, ExpTape Bit Count) -> Maybe (SkipResult Bit Count)
applySkip (Skip s e) (p, ExpTape leftTape tapePoint rightTape) | s ^. cstate == p
  = matchPoints (s^.c_point) tapePoint >>= \case
      --if we don't match the whole point, we can't care about the stuff on
      --the other side of the point, or we fail immediately
      Lremains remainP -> guard (s^.ls == []) >> matchBitTape (s^.rs) rightTape
        <&> \case
          Infinite -> SkippedOffEnd (Skip s e)
          --we only have to glom once because remainP can't match leftTape since
          --that would violate the input invariant
          NewTape t -> Skipped (e^.cstate) $ glomPointLeft $
            ExpTape (remainP:leftTape) (e^.c_point) ((e^.rs) `etApp` t)
      Rremains remainP -> guard (s^.rs == []) >> matchBitTape (s^.ls) leftTape
        <&> \case
          Infinite -> SkippedOffEnd (Skip s e)
          NewTape t -> Skipped (e^.cstate) $ glomPointRight $
            ExpTape ((e^.ls) `etApp` t) (e^.c_point) (remainP:rightTape)
      PerfectP -> bisequence (matchBitTape (s^.ls) leftTape, matchBitTape (s^.rs) rightTape)
        <&> \case
          (Infinite, _) -> SkippedOffEnd (Skip s e)
          (_, Infinite) -> SkippedOffEnd (Skip s e)
          (NewTape newL, NewTape newR) -> Skipped (e^.cstate) $
            ExpTape ((e^.ls) `etApp` newL) (e^.c_point) ((e^.rs) `etApp` newR)
--if the phases don't match, we fail right away
applySkip _ _ = Nothing

--we want to be able to apply a skip of counts to an ExpTape _ Count but also a
--skip of counts to an ExpTape _ Nat

-- the data type storing various proven skips associated with a machine
type SkipBook s = Map (Phase, s) (Skip s)

initTransSkip :: Edge -> Trans -> Set (Skip Bit)
initTransSkip (p, b) Halt = undefined
initTransSkip (p, b) (Step q c d) | p == q = undefined
initTransSkip (p, b) (Step q c d) = one $ Skip
  (Config p [] (b, Specific 1, L) [])
  undefined

initBook :: Turing -> SkipBook Bit
initBook t = undefined

--the results should be
--  how many machines halted
--    the longest running N machines
--    the most ones N machines
--  how many ran forever, with which kind of proof
--  how many ran out of time
--  and keep a certain number thereof
data Results a = Results
  { _haltCount :: Int
    , _longestRun :: Maybe (Int, Turing, a)
    , _mostOnes :: Maybe (Int, Turing, a)
  , _provenForever :: Int
    , _haltUnreachable :: Int
    , _cycledCount :: Int
    , _infinityN :: Int
  , _unproven :: Int
    , _unprovenExamples :: [(Turing, SimState a)]
  } deriving (Show, Eq, Ord, Generic)
instance NFData a => NFData (Results a)

$(makeLenses ''TMState)
$(makeLenses ''SimState)
$(makeLenses ''Results)

mirrorTMState :: TMState Tape -> TMState Tape
mirrorTMState (TMState p t) = TMState p $ mirrorTape t

mirrorSimState :: SimState Tape -> SimState Tape
mirrorSimState (SimState steps slow fast)
  = SimState steps (mirrorTMState slow) (mirrorTMState fast)

instance Eq a => AsEmpty (Results a) where
  _Empty = only $ Results
    { _haltCount = 0
      , _longestRun = Nothing
      , _mostOnes = Nothing
    , _provenForever = 0
      , _haltUnreachable = 0
      , _cycledCount = 0
      , _infinityN = 0
    , _unproven = 0
      , _unprovenExamples = []
    }
--number of unproven examples to keep
keepNum :: Int
keepNum = 3

addResult :: Turing -> SimResult Tape -> Results Tape -> Results Tape
addResult turing (Halted steps tape) r =
  addHalter $ addLongest $ addOnesiest (ones tape) r where
    addLongest r = case r ^. longestRun of
      Nothing -> r & longestRun ?~ (steps, turing, tape)
      Just (longestSteps, _, _) -> if steps > longestSteps
        then r & longestRun ?~ (steps, turing, tape) else r
    addOnesiest ones r = case r ^. mostOnes of
      Nothing -> r & mostOnes ?~ (ones, turing, tape)
      Just (mostOneCount, _, _) -> if ones > mostOneCount
      then r & mostOnes ?~ (ones, turing, tape) else r
    addHalter = haltCount +~ 1
addResult _ (ContinueForever proof) r =
  r & provenForever +~ 1 & proof2lens proof +~ 1 where
    proof2lens (HaltUnreachable _) = haltUnreachable
    proof2lens (Cycle _ _) = cycledCount
    proof2lens (OffToInfinityN _ _) = infinityN
addResult turing (Continue state) r = let r' = r & unproven +~ 1 in
  if r' ^. unproven > keepNum then r'
    else r' & unprovenExamples %~ ((:) (turing,state))

-- low priority todo :: filter out the machines which have duplicate states
-- creates a list of the various Turing machines that could result from filling
-- in the specified unknown edge, reducing via symmetry - if there are multiple
-- unused states, only sends us to the lowest numbered one
-- does not check that the edge is unknown, a precondition of correctness
branchOnEdge :: Edge -> Turing -> [Turing]
branchOnEdge e@(Phase newPhase, _) (Turing n m) = filter (not . isSmallerMachine) candidates where
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
  used i = is _Just (m ^. at (Phase i, False))
        || is _Just (m ^. at (Phase i, True))
        || i == newPhase
  equalJusts (Just a) (Just b) = a == b
  equalJusts _ _ = False
  equalStates m i j =
    (m ^. at (i, False)) `equalJusts` (m ^. at (j, False))
    &&
    (m ^. at (i, True)) `equalJusts` (m ^. at (j, True))
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
startMachine0 n = Turing n $ one ((Phase 0, False), (Step (Phase 1) False R))
startMachine1 :: Int -> Turing
startMachine1 1 = uni1Machine
startMachine1 n = Turing n $ one ((Phase 0, False), (Step (Phase 1) True R))
--for n=1 if you don't halt right away, you are doomed to loop forever
uni1Machine :: Turing
uni1Machine = Turing 1 $ one ((Phase 0, False), Halt)

collision :: Eq a => SimState a -> Bool
collision (SimState steps slow fast) = steps > 1 && slow == fast

getSteps :: SimState a -> (Steps, Steps)
getSteps (SimState steps _ _) = (steps `div` 2, steps)

--step limit, machine to start with
simulate :: Int -> Turing -> Results Tape
simulate limit startMachine = loop (startMachine, initSimState) [] Empty where
  -- current machine and state, next (machine&state)s, previous Results, returns updated Results
  loop :: (Turing, SimState Tape) -> [(Turing, SimState Tape)] -> Results Tape -> Results Tape
  loop (t, s@(collision -> True)) todoList !rs
    = --trace "added cycle" $
      recurse todoList $ addResult t (ContinueForever $ uncurry Cycle $ getSteps s) rs
  loop (t, s@(SimState ( ((\stepsTaken -> stepsTaken > limit) -> True)) _ _)) todoList !rs =
    -- if rs ^. unprovenExamples == [] then trace (show steps <> "\n") $
    --     recurse todoList $ addResult t (Continue s) rs
    --   else
        recurse todoList $ addResult t (Continue s) rs
  loop (t, s@(SimState stepsTaken slow fast)) todoList !rs = case proveForever t s of
    Just proof -> --trace "added infinity" $
      recurse todoList $ addResult t (ContinueForever proof) rs
    Nothing -> let newStepsTaken = stepsTaken+1 in
      case simStep t fast of
        Unknown e -> --trace ("branched on " <> show e) $
          recurse ((toList $ (,s) <$> branchOnEdge e t) ++ todoList) rs
        Stopped _ tape -> recurse todoList $ addResult t (Halted newStepsTaken tape) rs
        Stepped _ newFast -> let
          newSlow = if newStepsTaken `mod` 2 == 0  then forceAdvance t slow else slow
          newState = SimState newStepsTaken newSlow newFast
          in
          loop (t, newState) todoList rs
  forceAdvance t s = case simStep t s of
    Stepped _ newState -> newState
    _ -> error "forceAdvanced a state that doesn't advance"
  recurse [] result = result
  recurse (x : xs) result = loop x xs result

simulateWithSkips :: Int -> Turing -> Results (ExpTape Bit Int)
simulateWithSkips limit startMachine = loop (startMachine, initExpSimState False, initBook startMachine) [] Empty where
  loop :: (Turing, SimState (ExpTape Bit Int), SkipBook Bit)
    -> [(Turing, SimState (ExpTape Bit Int), SkipBook Bit)]
    -> Results (ExpTape Bit Int) -> Results (ExpTape Bit Int)
  loop = undefined


proveForever :: Turing -> SimState Tape -> Maybe HaltProof
proveForever = infiniteCycle

infiniteSimLimit :: Steps
infiniteSimLimit = 20

infiniteCycle :: Turing -> SimState Tape -> Maybe HaltProof
infiniteCycle t s = infiniteRight t s <|> infiniteLeft t s

infiniteRight :: Turing -> SimState Tape -> Maybe HaltProof
infiniteRight t (SimState originalSteps _ mState@(TMState startPhase (Tape startLs False [])))
  = step 0 0 0 mState where
  -- first arg counts number of steps taken in this halting proof
  -- second arg counts distance left or right from our starting point,
  -- left is negative, right is positive
  -- third arg counts max leftward distance (in positive terms)
  step :: Steps -> Int -> Int -> TMState Tape -> Maybe HaltProof
  --we hit our step limit
  step ((\i -> i >= infiniteSimLimit) -> True) _ _ _ = Nothing
  --here, distance is negative, so we just simulate another step
  step steps dist@((\d -> d <= 0) -> True) maxL s = stepRecurse steps dist maxL s
  --here, distance is positive, so we have a chance to fulfull the conditions
  --to prove infinite rightward movement
  step steps dist maxL s@(TMState (((==) startPhase) -> True) (Tape ls False [])) =
    if take maxL ls == take maxL startLs then Just $ OffToInfinityN originalSteps R
    else stepRecurse steps dist maxL s
  step steps dist maxL s = stepRecurse steps dist maxL s
  stepRecurse steps dist maxL s = case simStep t s of
    Stepped L s' -> step (steps + 1) (dist - 1) (newMax maxL (dist - 1)) s'
    Stepped R s' -> step (steps + 1) (dist + 1) maxL s'
    _ -> Nothing
  --first arg is old max, second arg is (signed) distance
  --max can only be beaten by a negative distance, since it's the farthest left
  newMax :: Int -> Int -> Int
  newMax oldMax ((\i -> i >= 0) -> True) = oldMax
  newMax oldMax (negate -> newPosDist) = max oldMax newPosDist
infiniteRight _ _ = Nothing

infiniteLeft :: Turing -> SimState Tape -> Maybe HaltProof
infiniteLeft t s = mirrorHaltProof <$> infiniteRight (mirrorTuring t) (mirrorSimState s)

dispTMState :: TMState Tape -> Text
dispTMState (TMState (Phase i) tape) = "phase: " <> show i <> " tape: " <> dispTape tape

dispSimState :: SimState Tape -> Text
dispSimState (SimState steps slow fast) = "steps: " <> showInt3Wide steps
  <> "\nslow: " <> dispTMState slow
  <> "\nfast: " <> dispTMState fast

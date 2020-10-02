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

import Util
import Turing
import Tape
import ExpTape --(ExpTape(..), Location(..), _Side, _One, glomPointLeft, glomPointRight, glomPoint, etApp)
import Skip
import Config
import Count

--Pieces: turing machines with unknown edges
-- a simulator that does the usual simulate forward, while branching on unknown edges, according to
-- certain symmetry
-- a more powerful infinity prover
-- a Results type and an aggregator that adds to the results

data TMState a = TMState { _phase :: Phase, _tape :: a} deriving (Eq, Ord, Show, Generic)
instance NFData a => NFData (TMState a)

initTMState :: TMState Tape
initTMState = TMState (Phase 0) (Tape [] False [])

initExpTMState :: s -> TMState (ExpTape s InfCount Location)
initExpTMState s = TMState (Phase 0) (ExpTape [(s, Infinity)] (s, One) [(s, Infinity)])

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

initExpSimState :: s -> SimState (ExpTape s InfCount Location)
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

--either we skipped ahead to a new Phase and Tape or we might've proved infinity
data SkipResult s c l = Skipped Phase (ExpTape s c l) | SkippedOffEnd (Skip s) deriving (Eq, Ord, Show, Generic)

dispSkipResult :: SkipResult Bit InfCount Location -> Text
dispSkipResult (SkippedOffEnd _) = "skipped off end!"
dispSkipResult (Skipped p tape) = "skipped to phase: " <> dispPhase p <> " and tape " <> dispExpTape tape

--returns nothing if the skip is inapplicable, else returns a new tape
--the fact that the type is bit is only used when running off the tape, but for now I don't want to
--generalize that out (also ExpTape would have to be generalized)
applySkip :: Skip Bit -> (Phase, ExpTape Bit InfCount Location) -> Maybe (SkipResult Bit InfCount Location)
applySkip skip@(Skip s e _ _) (p, ExpTape leftT pointT rightT) | s ^. cstate == p
  = packageResult =<< runEquationState intermediate where
    --intermediate :: EquationState Bit _
    intermediate = matchPoints (s ^. c_point) pointT >>= \case
      Lremains remainP -> matchSides (remainP : leftT) rightT
      Rremains remainP -> matchSides leftT (remainP : rightT)
      PerfectP -> matchSides leftT rightT
    matchSides left right = bisequence (matchBitTape (s^.ls) left, matchBitTape (s^.rs) right)
    --packageResult :: (Map BoundVar InfCount, Map TapeVar Bit, _) -> Maybe (SkipResult Bit InfCount Location)
    packageResult (boundVs, tapeVs, (tapeInfL, tapeInfR)) = case (tapeInfL, tapeInfR) of
      (Infinite, _) -> Just $ SkippedOffEnd skip
      (_, Infinite) -> Just $ SkippedOffEnd skip
      (NewTape newLs, NewTape newRs) -> Just $ Skipped (e^.cstate) $ glomPoint $ ExpTape
        ((invariantifyList $ updateList boundVs tapeVs $ NotInfinity <$$> e^.ls) `etApp` newLs)
        (updatePoint boundVs tapeVs $ e ^. c_point)
        ((invariantifyList $ updateList boundVs tapeVs $ NotInfinity <$$> e^.rs) `etApp` newRs)
    updateInfCount :: Map BoundVar InfCount -> InfCount -> InfCount
    updateInfCount _m Infinity = Infinity
    updateInfCount m (NotInfinity c) = updateCount m c
    updateCount :: Map BoundVar InfCount -> Count -> InfCount
    updateCount m (Count n as (MonoidalMap xs))
      = (NotInfinity $ Count n as Empty) <> foldMap (updateVar m) (assocs xs)
    deVarOr :: Map TapeVar s -> VarOr s -> s
    deVarOr _m (NotVar s) = s
    deVarOr m (Var v) = case m^.at v of
      Just s -> s
      Nothing -> error "a tape var wasn't mapped in a skip"
    updateVar :: Map BoundVar InfCount -> (BoundVar, Sum Natural) -> InfCount
    updateVar m (x, (Sum n)) = n `nTimesCount` getVar m x
    getVar :: Map BoundVar InfCount -> BoundVar -> InfCount
    getVar m x = case m^.at x of
      Just c -> c
      Nothing -> error "a bound var wasn't mapped in a skip"
    updatePoint :: Map BoundVar InfCount -> Map TapeVar s
      -> (VarOr s, Location Count) -> (s, Location InfCount)
    updatePoint bs ts = (_2. _Side . _1 %~ updateCount bs) . (_1 %~ deVarOr ts)
    updateList :: Map BoundVar InfCount -> Map TapeVar s
      -> [(VarOr s, InfCount)] -> [(s, InfCount)]
    updateList bs ts = fmap $ bimap (deVarOr ts) (updateInfCount bs)
applySkip _ _ = Nothing

--we want to be able to apply a skip of counts to an ExpTape _ Count but also a
--skip of counts to an ExpTape _ Nat

--the skip that results from the atomic transition given an edge leading to a
--transition of the specified Phase, Bit, Dir
oneStepSkip :: Edge -> Phase -> Bit -> Dir -> Skip Bit
oneStepSkip (p, b) q c L = Skip
  (Config p [(Var (TapeVar 0), finiteCount 1)] (NotVar b, One) [])
  (Config q [] (Var (TapeVar 0), One) [(NotVar c, finiteCount 1)])
  (finiteCount 1)
  False
oneStepSkip (p, b) q c R = Skip
  (Config p [] (NotVar b, One) [(Var (TapeVar 0), finiteCount 1)])
  (Config q [(NotVar c, finiteCount 1)] (Var (TapeVar 0), One) [])
  (finiteCount 1)
  False

--the skip that results from an atomic transition which transitions a phase to itself
--writing the given bit and dir
infiniteSkip :: Edge -> Bit -> Dir -> Skip Bit
infiniteSkip (p, b) c L = Skip
  (Config p [(Var (TapeVar 0), finiteCount 1)] (NotVar b, Side (newBoundVar 0) R) [])
  (Config p [] (Var (TapeVar 0), One) [(NotVar c, newBoundVar 0)])
  (newBoundVar 0)
  False
infiniteSkip (p, b) c R = Skip
  (Config p [] (NotVar b, Side (newBoundVar 0) L) [(Var (TapeVar 0), finiteCount 1)])
  (Config p [(NotVar c, newBoundVar 0)] (Var (TapeVar 0), One) [])
  (newBoundVar 0)
  False

initTransSkip :: Edge -> Trans -> Set (Skip Bit)
initTransSkip e@(p, _b) Halt = one $ oneStepSkip e p True R
initTransSkip e@(p, _b) (Step q c d) | p == q = fromList
  [ oneStepSkip e q c d
  , infiniteSkip e c d
  ]
initTransSkip e (Step q c d) = one $ oneStepSkip e q c d

--the data type storing various proven skips associated with a machine
--the "Phase, s" is the Phase on start and the "s" that the point is made of
--it's a maybe because some skips have a var under the point
type SkipBook s = Map (Phase, Maybe s) (Set (Skip s))

addSkipToBook :: (Ord s) => Skip s -> SkipBook s -> SkipBook s
addSkipToBook skip = atE (skip^.start.cstate, skip^?start.c_point._1._NotVar)
  . contains skip .~ True

initBook :: Turing -> SkipBook Bit
initBook (Turing _n trans) = appEndo (foldMap (Endo . addSkipToBook) skips) $ Empty where
  skips = foldMap (uncurry initTransSkip) $ assocs trans

lookupSkips :: (Ord s) => (Phase, s) -> SkipBook s -> Set (Skip s)
lookupSkips (p, s) book = book ^. atE (p, Just s) <> book ^. atE (p, Nothing)

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
    , _backwardSearches :: Int
    , _backwardExamples :: [Turing]
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
      , _backwardSearches = 0
      , _backwardExamples = []
    , _unproven = 0
      , _unprovenExamples = []
    }
--number of unproven examples to keep, used also for backward Examples
keepNum :: Int
keepNum = 3

addResult :: Turing -> SimResult Tape -> Results Tape -> Results Tape
addResult turing (Halted steps tape) r = --(if turing == bb3test then traceShow h else id)
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
addResult turing (ContinueForever proof) r = -- (if turing == bb3test then trace "found1" else id)
  r & provenForever +~ 1 & proof2lens proof +~ 1 & special proof where
    proof2lens (HaltUnreachable _) = haltUnreachable
    proof2lens (Cycle _ _) = cycledCount
    proof2lens (OffToInfinityN _ _) = infinityN
    proof2lens (BackwardSearch) = backwardSearches
    special BackwardSearch = --if r ^. backwardSearches > keepNum then id else
      backwardExamples %~ ((:) turing)
    special _ = id
addResult turing (Continue state) r = --(if turing == bb3test then trace "found2" else id) $
  let r' = r & unproven +~ 1 in
  if r' ^. unproven > keepNum then r'
    else r' & unprovenExamples %~ ((:) (turing,state))

--
bb3test :: Turing
bb3test = Turing {states = 3, transitions = fromList
  [((Phase 0, False), Step (Phase 1) True  R)
  ,((Phase 0, True ), Halt)                   -- check check check
  ,((Phase 1, False), Step (Phase 1) True  L) --                 - 3 --check
  ,((Phase 1, True ), Step (Phase 2) False L) --                 - 2 --check
  ,((Phase 2, False), Step (Phase 0) True  R) -- second-to-last  - 1 --check
  ,((Phase 2, True ), Step (Phase 2) True  R) --last trans added - 0 --check
  ]}
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
  recurse ((t,s) : xs) result = case staticAnalyze t of
    Just proof -> recurse xs $ addResult t (ContinueForever proof) result
    Nothing -> loop (t,s) xs result

-- simulateWithSkips :: Int -> Turing -> Results (ExpTape Bit Int)
-- simulateWithSkips limit startMachine = loop (startMachine, initExpSimState False, initBook startMachine) [] Empty where
--   loop :: (Turing, SimState (ExpTape Bit Int), SkipBook Bit)
--     -> [(Turing, SimState (ExpTape Bit Int), SkipBook Bit)]
--     -> Results (ExpTape Bit Int) -> Results (ExpTape Bit Int)
--   loop = undefined

--halting analyses that can be performed without simulating the machine
staticAnalyze :: Turing -> Maybe HaltProof
staticAnalyze = backwardSearch
-- staticAnalyze = const Nothing

--attempting to prove the machine runs forever starting at a given state
proveForever :: Turing -> SimState Tape -> Maybe HaltProof
proveForever t s@(SimState stepsTaken _ _) = infiniteCycle (min stepsTaken infiniteSimLimit) t s

infiniteCycle :: Int -> Turing -> SimState Tape -> Maybe HaltProof
infiniteCycle limit t s = infiniteRight limit t s <|> infiniteLeft limit t s

infiniteRight :: Int -> Turing -> SimState Tape -> Maybe HaltProof
infiniteRight limit t (SimState originalSteps _ mState@(TMState startPhase (Tape startLs False [])))
  = step 0 0 0 mState where
  -- first arg counts number of steps taken in this halting proof
  -- second arg counts distance left or right from our starting point,
  -- left is negative, right is positive
  -- third arg counts max leftward distance (in positive terms)
  step :: Steps -> Int -> Int -> TMState Tape -> Maybe HaltProof
  --we hit our step limit
  step ((\i -> i >= limit) -> True) _ _ _ = Nothing
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
infiniteRight _ _ _ = Nothing

infiniteLeft :: Int -> Turing -> SimState Tape -> Maybe HaltProof
infiniteLeft limit t s = mirrorHaltProof <$> infiniteRight limit (mirrorTuring t) (mirrorSimState s)

dispTMState :: TMState Tape -> Text
dispTMState (TMState (Phase i) tape) = "phase: " <> show i <> " tape: " <> dispTape tape

dispSimState :: SimState Tape -> Text
dispSimState (SimState steps slow fast) = "steps: " <> showInt3Wide steps
  <> "\nslow: " <> dispTMState slow
  <> "\nfast: " <> dispTMState fast

--runs a backward search from each halting state to see if it can reach a contradiction
--if we show that all ways to halt don't have paths leading into them from valid tapes
--then the halt state will never be reached
--of course no such procedure can be complete, so we put a finite depth on the search and
--give up after a while
backwardSearch :: Turing -> Maybe HaltProof
backwardSearch (Turing n trans) | length trans < (n*2) - 1 = Nothing
backwardSearch (Turing n trans) = recurse 0 $ fromList $ (, Min 0) <$> (initState <$> unusedEdges) where
  unusedEdges :: [Edge]
  unusedEdges = NE.filter (\e -> let t = trans ^. at e in t == Nothing || t == Just Halt) $ uniEdge n
  initState :: Edge -> (Phase,Tape)
  initState (p, b) = (p, Tape [] b [])
  loop :: Int -> ((Phase, Tape), Int) -> MonoidalMap (Phase, Tape) (Min Int) -> Maybe HaltProof
  loop globalSteps _ _ | globalSteps > backwardSearchGlobalLimit = Nothing
  loop _ (_, localSteps) _ | localSteps > backwardSearchSingleLimit = Nothing
  loop globalSteps (tape, localSteps) rest
    = case fromList $ (,Min $ localSteps+1) <$> backSteps tape of
      Empty -> recurse globalSteps rest
      possibilities -> recurse (globalSteps + 1) (possibilities <> rest)
  recurse :: Int -> MonoidalMap (Phase,Tape) (Min Int) -> Maybe HaltProof
  recurse _globalSteps Empty = Just $ BackwardSearch
  recurse globalSteps (deleteFindMin -> (f, rest)) = loop globalSteps (second getMin f) rest

  --this is subtle: it doesn't account for getting to your current undefined transition
  --by taking another undefined transition, but you must be able to reach _some_ undefined transition
  --by taking only real transitions or you will stay taking defined transitions forever, thus never halting
  transList = assocs trans
  candidateTrans :: Phase -> [(Edge, Trans)]
  candidateTrans p = filter ((== Just p) . getPhase . snd) transList
  --given a tape, returns all tapes that could result in the given tape
  backSteps :: (Phase,Tape) -> [(Phase,Tape)]
  backSteps (p, t) = mapMaybe (backStep (p,t)) $ candidateTrans p

  --precondition: the phase given and the getPhase of the Trans are the same
  backStep :: (Phase,Tape) -> (Edge,Trans) -> Maybe (Phase, Tape)
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

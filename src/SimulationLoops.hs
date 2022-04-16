module SimulationLoops where

import Relude hiding (inits)
import qualified Relude.Unsafe as Unsafe
import Control.Lens
import Data.List (maximumBy, foldl1, maximum, minimum)
import Data.List.NonEmpty (inits)
import Safe.Exact
import Prettyprinter
import qualified Data.List.NonEmpty as NE ((<|))
import qualified Data.Set as S 

import Turing
import ExpTape
import Count
import HaltProof
import Results
import Glue
import SimulateSkip
import Skip
import Util
import Control.Exception (assert)
import Relude.Unsafe ((!!))
import Display
import Safe.Partial
import Notation


type SimOneAction = Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState

data MultiResult a = UnknownEdge Edge
                 | Result (SimResult (ExpTape Bit InfCount))
                 | NewState a
                    deriving (Eq, Ord, Show, Functor)
type SimMultiAction = Turing -> SimState -> MultiResult SimState

instance Applicative MultiResult where
  pure = return
  x1 <*> x2 = x1 >>= flip fmap x2

instance Monad MultiResult where
  return = NewState
  (>>=) :: MultiResult a -> (a -> MultiResult b) -> MultiResult b
  k >>= f = case k of
    NewState a -> f a
    UnknownEdge e -> UnknownEdge e
    Result r -> Result r

concatActions :: NonEmpty SimOneAction -> SimOneAction
concatActions actions machine = foldl1 (>=>) ((&) machine <$> actions)

type OneLoopRes = (SimResult (ExpTape Bit InfCount), NonEmpty SimState)

simulateOneMachineOuterLoop :: NonEmpty SimOneAction -> Turing -> SimState -> OneLoopRes 
simulateOneMachineOuterLoop updateFuncs startMachine
  = iterateEither (concatActions updateFuncs startMachine) 
  where
    iterateEither :: (a -> Either r a) -> a -> (r, NonEmpty a)
    iterateEither k init = case k init of
      Left r -> (r, one init)
      Right next -> (NE.<|) init <$> iterateEither k next

simOneFromStartLoop :: NonEmpty SimOneAction -> Turing -> OneLoopRes 
simOneFromStartLoop updateFuncs startMachine 
  = simulateOneMachineOuterLoop updateFuncs startMachine (initSkipState startMachine) 

simulateManyMachinesOuterLoop :: (Turing -> Maybe HaltProof) -> NonEmpty SimMultiAction -> Turing -> [(Turing, SimResult (ExpTape Bit InfCount))]
simulateManyMachinesOuterLoop staticAnal updateFuncs startMachine = loop (startMachine, startState) [] [] where
  startState :: SimState
  startState = initSkipState startMachine
  bigUpdateFunc :: Turing -> SimState -> MultiResult SimState
  bigUpdateFunc machine = foldl1 (>=>) ((&) machine <$> updateFuncs)
  loop :: (Turing, SimState) -> [(Turing, SimState)]
    -> [(Turing, SimResult (ExpTape Bit InfCount))] -> [(Turing, SimResult (ExpTape Bit InfCount))]
  loop cur@(curMachine, curState) todo !prevRes = --trace (show $ machineToNotation curMachine) $ --force $
   case uncurry bigUpdateFunc cur of
    NewState newState -> loop (curMachine, newState) todo prevRes
    Result !result -> --trace ("got result: " <> show result) $ 
      recurse todo ((curMachine, result) : prevRes)
    UnknownEdge e -> let 
        candidateMachines = branchOnEdge e curMachine
        mbProofs = staticAnal <$> candidateMachines
        makeRes m = \case 
          Nothing -> Left m 
          (Just hp) -> Right (m, ContinueForever hp)
        -- musing 31 dec 
        -- worry: there might be machines that aren't getting counted, making the tree generation
        -- correct is very important. sometimes we branch to only 4 machines, in particular?
        (newMachines, reses) = partitionEithers $ uncurry makeRes <$> zip candidateMachines mbProofs 
      in
        recurse ((makeNewState e curState <$> newMachines) <> todo) (reses <> prevRes)
  makeNewState :: Edge -> SimState -> Turing -> (Turing, SimState)
  makeNewState edge state machine = (machine, state & s_book %~ updateBook edge machine)
  recurse :: [(Turing, SimState)] -> [(Turing, SimResult (ExpTape Bit InfCount))] -> [(Turing, SimResult (ExpTape Bit InfCount))]
  --recurse todos results | trace ("length todos: " <> show (length todos) <> " length results: " <> show (length results) <> " and last result" <> show (viaNonEmpty head results))    False = undefined
  recurse [] results = --trace "recursed empty" 
    results
  recurse (next : todos) results = --trace ("looping to next:" <> showP (fst next) <> "\nstack depth:" <> showP (length todos))
    --(if (length results `mod` 1000 == 0) then trace ("reslength:" <> show (length results)) else id)
    --deepseq results $ 
      loop next todos results

liftOneToMulti :: SimOneAction -> SimMultiAction
liftOneToMulti action machine state = case action machine state of
  Left res -> Result res
  Right newState -> NewState newState

liftModifyState :: (SimState -> SimState) -> (Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState)
liftModifyState f _t = Right . f

liftModifyStateMulti :: (SimState -> SimState) -> SimMultiAction
liftModifyStateMulti = liftOneToMulti . liftModifyState

runIfCond :: (SimState -> Bool) -> SimOneAction -> SimOneAction
runIfCond cond act machine state = if cond state 
  then act machine state 
  else pure state

runAtCount :: Int -> SimOneAction -> SimOneAction
runAtCount n = runIfCond (\state -> 
  --trace ("goal:" <> show n <> " actual: " <> show (state ^. s_counter))
  (state ^. s_counter == n))

runAtCounts :: [Int] -> SimOneAction -> SimOneAction 
runAtCounts xs = let setXs = S.fromList xs in 
  runIfCond (\state -> 
    (state ^. s_counter) `S.member` setXs)

addSkipToStateOrInf :: Skip Count Bit -> SkipOrigin Bit -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
addSkipToStateOrInf skip origin state = if skipGoesForever skip && skipAppliedInHist skip (state ^. s_history)
  then Left (ContinueForever (SkippedToInfinity (state ^. s_steps) skip))
  else Right $ state & s_book %~ addSkipToBook skip origin

--this is something for simulating one machine where you tell me how to handle an unknown edge
--and I do that
simulateStepOneMachine :: Partial => (Edge -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState) 
  -> Int -> Turing -> SimState 
  -> Either (SimResult (ExpTape Bit InfCount)) SimState
simulateStepOneMachine handleUnknown limit machine state@(SimState ph tape book steps skipTrace hist histSet counter curDisp dispHist rsHist) 
  = if counter > limit
    then Left $ Continue steps ph tape curDisp
    else --trace ("counter:" <> show counter) $ 
    case skipStep machine book ph tape of
    Unknown e -> handleUnknown e state 
    MachineStuck -> Left MachineStuckRes
    Stopped c newTape _skipUsed newDisp rs -> Left $ Halted (steps + infCountToInt c) newTape (curDisp + dispToInt newDisp)
    Stepped c newPh newTape skipUsed newDisp rs -> case c of
      Infinity -> Left $ ContinueForever (SkippedToInfinity steps skipUsed)
      c -> Right $ SimState newPh newTape book (steps + infCountToInt c) (skipUsed : skipTrace)
        hist histSet (counter + 1) (curDisp + dispToInt newDisp) dispHist (addToRRSH rs rsHist)

--this one essentially asserts there is no unknown edge, or otherwise crashes
simulateStepTotalLoop :: Partial => Int -> Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
simulateStepTotalLoop = simulateStepOneMachine (\e _state -> error $ "edge undefined" <> show e)

simulateStepUntilUnknown :: Partial => Int -> Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
simulateStepUntilUnknown = simulateStepOneMachine handle where 
  handle _e state = Left $ Continue (state ^. s_steps) (state ^. s_phase) (state ^. s_tape) (state ^. s_displacement)

--this is pretty copied from "simulateOneMachine"
simulateStepPartial :: Partial => Int -> SimMultiAction
simulateStepPartial limit machine (SimState ph tape book steps skipTrace hist histSet counter curDisp dispHist rsHist) = 
  --trace ("stepping bigStep: " <> showP counter <> " smallStep: " <> showP steps) $
  if counter > limit
  then Result $ Continue steps ph tape curDisp
  else case skipStep machine book ph tape of
    Unknown e -> UnknownEdge e
    MachineStuck -> error "machinestuck "
    Stopped c newTape _skipUsed newDisp rs -> Result $ Halted (steps + infCountToInt c) newTape (curDisp + dispToInt newDisp)
    Stepped c newPh newTape skipUsed newDisp rs -> --trace ("entered stepped, c:" <> showP c) $ 
      case c of
      Infinity -> Result $ ContinueForever (SkippedToInfinity steps skipUsed)
      c -> NewState $ SimState newPh newTape book (steps + infCountToInt c) (skipUsed : skipTrace)
        hist histSet (counter + 1) (curDisp + dispToInt newDisp) dispHist (addToRRSH rs rsHist)

gluePreviousTwoSkips :: SimState -> SimState
gluePreviousTwoSkips state = state & s_book .~ newBook where
  book = state ^. s_book
  newBook = case state ^. s_trace of
    [] -> book
    [_] -> book
    skip : prevSkip : _rest -> case glueSkips prevSkip skip of
      Left err -> error $ "used two skips in a row but couldn't glue:\n"
        <> "reason: " <> err <> "\n" <> show (pretty prevSkip)
        <> "\nsecond skip\n" <> show (pretty skip)
      Right gluedSkip -> addSkipToBook gluedSkip (Glued prevSkip skip) book

recordHist :: SimState -> SimState
recordHist state = state & s_reverse_history . reverseTapeHist %~ (histEnt :) where
  histEnt = (state ^. s_phase, state ^. s_tape)

recordDispHist :: SimState -> SimState
recordDispHist state = state & s_reverse_disp_history . reverseDispHist %~ (state ^. s_displacement :)

seenBeforeProof :: SimState -> Maybe HaltProof 
seenBeforeProof state = case state ^. s_history_set . at histEnt of
  Just prevStepCount -> Just $ Cycle prevStepCount curStepCount
  Nothing -> Nothing 
  where
  histEnt = (state ^. s_phase, state ^. s_tape)
  curStepCount = state ^. s_steps

updateHistSet :: SimOneAction 
updateHistSet _machine state = Right $ state & s_history_set . at histEnt ?~ curStepCount
  where
  histEnt = (state ^. s_phase, state ^. s_tape)
  curStepCount = state ^. s_steps

checkSeenBefore :: SimOneAction
checkSeenBefore _machine state = case seenBeforeProof state of 
  Just proof -> Left $ ContinueForever proof 
  Nothing -> Right $ state & s_history_set . at histEnt ?~ curStepCount
  where
  histEnt = (state ^. s_phase, state ^. s_tape)
  curStepCount = state ^. s_steps

--applies the skip to everything in the list, checks if any of them have just 
skipAppliedInHist :: Skip Count Bit -> TapeHist Bit InfCount -> Bool
skipAppliedInHist skip hist = any (has _Just) $ applySkip skip <$> getTapeHist hist

--checks whether we've put an infinity in some place on the tape that is not the two ends
--this is a hacky workaround to fix the fact that we currently don't know how to tell how 
--many steps an induction takes since it is an alternate way to tell whether a skip goes 
--forever 
tapePostInfinity :: ExpTape s InfCount -> Bool 
tapePostInfinity (ExpTape ls _p rs) = elem Infinity cs where 
  cs = snd <$> Unsafe.init ls ++ Unsafe.init rs

skipAppliesForeverInHist :: Skip Count Bit -> TapeHist Bit InfCount -> Either Text HaltProof
skipAppliesForeverInHist skip hist = case forevers of 
  [] -> Left "did not apply forever"
  --TODO the "idx" here is I think in big steps but it's sort of supposed to be in small steps
  (idx, _res) : _xs -> Right $ SkippedToInfinity idx skip 
  where 
  apps = let ans = mapMaybe (\(i, entry) -> (i,) <$> applySkip skip entry) (zip [0,1 ..] $ getTapeHist hist) in 
    --trace ("apps len " <> show (length ans)) 
    ans 
  forevers = filter (\(_i, res) -> --trace ("skipRes" <> showP (res)) $ 
    view hopsTaken res == Infinity || tapePostInfinity (view newTape res)) apps 
{-
A thing I need to be very careful about is the interaction between EndOfTape proof and the skipping parts of evaluation
If we skip over part of the evaluation that involves the maximum inward displacement, then we could assume we had a 
successful proof when we actually don't, and this is hard to catch. 
-}
atLeftOfTape :: ExpTape Bit InfCount -> Bool
atLeftOfTape (ExpTape ls _p _rs) = ls == [(Bit False, Infinity)]

atRightOfTape :: ExpTape Bit InfCount -> Bool
atRightOfTape (ExpTape _ls _p rs) = rs == [(Bit False, Infinity)]

{-
How this function works: 
1. only called when the machine is at the left side of the tape. 
2. finds the previous time the machine was at the left side of the tape. 
3. finds the maximum rightward displacement over that interval. 
4. if the leftmost bits of the tape are the same then and now, we have a proof!
5. (maybe future): check the condition again by brute force simulation

TODO this function is currently confusingly written to be interacting with the 
reverse histories, but probably should interact with the forward histories
TODO we currently duplicate the full 20 line function here which is 
pretty terrible, probably we should . . . not do that
-}

eotProof :: SimState -> Maybe HaltProof 
eotProof state = assert (atLeftOfTape $ state ^. s_tape) maybeProof
 where
  samePhase = (== state ^. s_phase)
  samePoint (ExpTape _ls oldPoint _rs) = oldPoint == point (state ^. s_tape)
  isCandidate (disp, (phase, tape)) 
    = samePhase phase && atLeftOfTape tape && samePoint tape && curDisp <= disp
  (curDisp :| dispList) = fromList $ state ^. s_reverse_disp_history . reverseDispHist
  maximumInwardList = fmap maximum $ tail $ inits dispList
  bitsToCheck = uncurry (-) <$> zipExact maximumInwardList dispList
  history = Unsafe.tail $ state ^. s_reverse_history . reverseTapeHist 
  toFilter :: [(Int, (Int, (Phase, ExpTape Bit InfCount)))]
  toFilter = zipExact bitsToCheck $ zipExact dispList history
  candidates = filter (isCandidate . view _2) toFilter
  -- candidates = filter (isCandidate . view _2) $ zipExact bitsToCheck $ 
  --   Unsafe.tail $ state ^. s_reverse_history . reverseTapeHist 
  -- int is from bitsToCheck
  checkProof :: (Int, (Int, (Phase, ExpTape Bit InfCount))) -> Maybe HaltProof
  checkProof (numBitsToCheck, (_disp, (_ph, oldTape))) = let
    getBits tapeHalf = takeExact numBitsToCheck $ 
      tapeHalfToBitList tapeHalf <> repeat (Bit False)
    in
    if getBits (right oldTape) == getBits (right $ state ^. s_tape)
      then Just $ OffToInfinityN (state ^. s_steps) L
      else Nothing
  maybeProof :: Maybe HaltProof
  maybeProof = viaNonEmpty head $ mapMaybe checkProof candidates

attemptEndOfTapeProof :: SimOneAction
attemptEndOfTapeProof _m state 
  = maybe (Right state) (Left . ContinueForever) $ eotProof state

otherEotProof :: SimState -> Maybe HaltProof
otherEotProof state = assert (atRightOfTape $ state ^. s_tape) maybeProof  
 where
  samePhase = (== state ^. s_phase)
  samePoint (ExpTape _ls oldPoint _rs) = oldPoint == point (state ^. s_tape)
  isCandidate (disp, (phase, tape)) = samePhase phase && atRightOfTape tape && samePoint tape && curDisp >= disp
  (curDisp :| dispList) = let ans = fromList $ state ^. s_reverse_disp_history . reverseDispHist in 
    --trace ("rev disps:\n" <> showP ans) 
    ans
  minimumInwardList = let ans = fmap minimum $ tail $ inits dispList in 
    --trace ("minIn:\n" <> showP ans) 
    ans 
  bitsToCheck = let ans = uncurry (-) <$> zipExact dispList minimumInwardList in 
    --trace ("bits to check:\n" <> showP ans) 
    ans
  history = Unsafe.tail $ state ^. s_reverse_history . reverseTapeHist 
  toFilter :: [(Int, (Int, (Phase, ExpTape Bit InfCount)))]
  toFilter = zipExact bitsToCheck $ zipExact dispList history
  candidates = filter (isCandidate . view _2) toFilter
  -- int is from bitsToCheck
  checkProof :: (Int, (Int, (Phase, ExpTape Bit InfCount))) -> Maybe HaltProof
  checkProof (numBitsToCheck, (disp, (_ph, oldTape))) = let
    getBits tapeHalf = takeExact numBitsToCheck $ tapeHalfToBitList tapeHalf <> repeat (Bit False)
    in
    if getBits (left oldTape) == getBits (left $ state ^. s_tape)
      then 
        --trace ("bits to check " <> show numBitsToCheck) $ 
        Just $ OffToInfinityN (state ^. s_steps) R
      else Nothing
  maybeProof :: Maybe HaltProof
  maybeProof = viaNonEmpty head $ mapMaybe checkProof candidates

attemptOtherEndOfTapeProof :: SimOneAction
attemptOtherEndOfTapeProof _machine state 
  = maybe (Right state) (Left . ContinueForever) $ otherEotProof state

loopSimulateSkip :: Int -> Turing -> OneLoopRes
loopSimulateSkip limit = simOneFromStartLoop $ pure $ simulateStepTotalLoop limit

simulateManyBasicLoop :: Int -> Turing -> [_]
simulateManyBasicLoop limit = simulateManyMachinesOuterLoop (const Nothing) $ simulateStepPartial limit
  :| (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof
  ])

loopForEndOfTapeGlue :: Int -> Turing -> OneLoopRes
loopForEndOfTapeGlue limit = simOneFromStartLoop $
    simulateStepTotalLoop limit :| [liftModifyState recordHist, liftModifyState recordDispHist, runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof]

simulateForTime :: Partial => Int -> Turing -> OneLoopRes
simulateForTime time = simOneFromStartLoop actionList where
  actionList = simulateStepTotalLoop (time + 1) :| [liftModifyState recordHist, liftModifyState recordDispHist]

getStateAfterTime :: Partial => Int -> Turing -> SimState
getStateAfterTime time turing = last $ simulateForTime time turing ^. _2

getTwoHistAfterTime :: Partial => Int -> Turing -> (TapeHist Bit InfCount, DispHist)
getTwoHistAfterTime stepCount turing 
  = (guessingState ^. s_history, guessingState ^. s_disp_history) 
  where
    guessingState = getStateAfterTime stepCount turing
  
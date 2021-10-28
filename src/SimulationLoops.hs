module SimulationLoops where

import Relude hiding (inits)
import qualified Relude.Unsafe as Unsafe
import Control.Lens
import Data.List (maximumBy, foldl1, maximum, minimum)
import Data.List.NonEmpty (inits)
import Prettyprinter
import qualified Data.List.NonEmpty as NE ((<|))

import Turing
import ExpTape
import Count
import HaltProof
import Results
import Glue
import SimulateSkip
import Induction
import Skip
import Util
import Control.Exception (assert)
import Safe.Exact
import Relude.Unsafe ((!!))
import Display


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

simulateOneMachineOuterLoop :: NonEmpty SimOneAction -> Turing -> OneLoopRes 
simulateOneMachineOuterLoop updateFuncs startMachine
  = iterateEither (concatActions updateFuncs startMachine) (initSkipState startMachine) where
    iterateEither :: (a -> Either r a) -> a -> (r, NonEmpty a)
    iterateEither k init = case k init of
      Left r -> (r, one init)
      Right next -> (NE.<|) init <$> iterateEither k next

simulateManyMachinesOuterLoop :: NonEmpty SimMultiAction -> Turing -> [(Turing, SimResult (ExpTape Bit InfCount))]
simulateManyMachinesOuterLoop updateFuncs startMachine = loop (startMachine, startState) [] [] where
  startState :: SimState
  startState = initSkipState startMachine
  bigUpdateFunc :: Turing -> SimState -> MultiResult SimState
  bigUpdateFunc machine = foldl1 (>=>) ((&) machine <$> updateFuncs)
  loop :: (Turing, SimState) -> [(Turing, SimState)]
    -> [(Turing, SimResult (ExpTape Bit InfCount))] -> [(Turing, SimResult (ExpTape Bit InfCount))]
  loop cur@(curMachine, curState) todo !prevRes = case uncurry bigUpdateFunc cur of
    NewState newState -> loop (curMachine, newState) todo prevRes
    Result result -> recurse todo ((curMachine, result) : prevRes)
    UnknownEdge e -> recurse ((makeNewState e curState <$> branchOnEdge e curMachine) <> todo) prevRes
  makeNewState :: Edge -> SimState -> Turing -> (Turing, SimState)
  makeNewState edge state machine = (machine, state & s_book %~ updateBook edge machine)
  recurse :: [(Turing, SimState)] -> [(Turing, SimResult (ExpTape Bit InfCount))] -> [(Turing, SimResult (ExpTape Bit InfCount))]
  recurse [] results = results
  recurse (next : todos) results = loop next todos results

liftOneToMulti :: SimOneAction -> SimMultiAction
liftOneToMulti action machine state = case action machine state of
  Left res -> Result res
  Right newState -> NewState newState

liftModifyState :: (SimState -> SimState) -> (Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState)
liftModifyState f _t = Right . f

liftModifyStateMulti :: (SimState -> SimState) -> SimMultiAction
liftModifyStateMulti = liftOneToMulti . liftModifyState

runIfCond :: (SimState -> Bool) -> SimOneAction -> SimOneAction
runIfCond cond act machine state = if cond state then act machine state else pure state

runAtCount :: Int -> SimOneAction -> SimOneAction
runAtCount n = runIfCond (\state -> state ^. s_counter == n)

addSkipToStateOrInf :: Skip Bit -> SkipOrigin Bit -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
addSkipToStateOrInf skip origin state = if skipGoesForever skip && skipAppliedInHist skip (state ^. s_history)
  then Left (ContinueForever (SkippedToInfinity (state ^. s_steps) skip))
  else Right $ state & s_book %~ addSkipToBook skip origin

--this is pretty copied from "simulateOneMachine"
simulateStepTotalLoop :: Int -> Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
simulateStepTotalLoop limit machine (SimState ph tape book steps trace hist histSet counter curDisp dispHist) = if steps > limit
  then Left $ Continue steps ph tape curDisp
  else case skipStep machine book ph tape of
  Unknown e -> error $ "edge undefined" <> show e
  MachineStuck -> error "machinestuck "
  Stopped c newTape _skipUsed newDisp -> Left $ Halted (steps + infCountToInt c) newTape (curDisp + dispToInt newDisp)
  Stepped c newPh newTape skipUsed newDisp -> case c of
    Infinity -> Left $ ContinueForever (SkippedToInfinity steps skipUsed)
    c -> Right $ SimState newPh newTape book (steps + infCountToInt c) (skipUsed : trace)
      hist histSet (counter + 1) (curDisp + dispToInt newDisp) dispHist

--this is pretty copied from "simulateOneMachine"
simulateStepPartial :: Int -> SimMultiAction
simulateStepPartial limit machine (SimState ph tape book steps trace hist histSet counter curDisp dispHist) = if steps > limit
  then Result $ Continue steps ph tape curDisp
  else case skipStep machine book ph tape of
  Unknown e -> UnknownEdge e
  MachineStuck -> error "machinestuck "
  Stopped c newTape _skipUsed newDisp -> Result $ Halted (steps + infCountToInt c) newTape (curDisp + dispToInt newDisp)
  Stepped c newPh newTape skipUsed newDisp -> case c of
    Infinity -> Result $ ContinueForever (SkippedToInfinity steps skipUsed)
    c -> NewState $ SimState newPh newTape book (steps + infCountToInt c) (skipUsed : trace)
      hist histSet (counter + 1) (curDisp + dispToInt newDisp) dispHist

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
recordHist state = state & s_history %~ (histEnt :) where
  histEnt = (state ^. s_phase, state ^. s_tape)

recordDispHist :: SimState -> SimState
recordDispHist state = state & s_disp_history %~ (state ^. s_displacement :)

checkSeenBefore :: SimOneAction
checkSeenBefore _machine state = case state ^. s_history_set . at histEnt of
  Just prevStepCount -> Left $ ContinueForever $ Cycle prevStepCount curStepCount
  Nothing -> Right $ state & s_history_set . at histEnt ?~ curStepCount
  where
  histEnt = (state ^. s_phase, state ^. s_tape)
  curStepCount = state ^. s_steps

--applies the skip to everything in the list, checks if any of them have just 
skipAppliedInHist :: Skip Bit -> [(Phase, ExpTape Bit InfCount)] -> Bool
skipAppliedInHist skip hist = any (has _Just) $ applySkip skip <$> hist

attemptInductionGuess :: Turing -> SimState -> Either (SimResult (ExpTape Bit InfCount)) SimState
attemptInductionGuess machine state = case guessInductionHypothesis hist of
  Nothing -> Right state
  --try to prove the skip by induction 
  Just skip -> trace ("guessed a skip:\n" <> show (pretty skip)) $
    case proveInductively 20 machine (state ^. s_book) skip (BoundVar 0) of
      Left fail -> trace (toString fail) $ Right state
      Right skipOrigin -> addSkipToStateOrInf skip skipOrigin state
        -- if skipGoesForever skip && skipAppliedInHist skip hist 
        -- then Left (ContinueForever (SkippedToInfinity (state ^. s_steps) skip))
        -- else Right $ state & s_book %~ addSkipToBook skip skipOrigin 
  where
    hist = reverse (state ^. s_history)

{-
A thing I need to be very careful about is the interaction between EndOfTape proof and the skipping parts of evaluation
If we skip over part of the evaluation that involves the maximum inward displacement, then we could assume we had a 
successful proof when we actually don't, and this is hard to catch. 
-}
atLeftOfTape :: ExpTape Bool InfCount -> Bool
atLeftOfTape (ExpTape ls _p _rs) = ls == [(False, Infinity)]

atRightOfTape :: ExpTape Bool InfCount -> Bool
atRightOfTape (ExpTape _ls _p rs) = rs == [(False, Infinity)]

{-
How this function works: 
1. only called when the machine is at the left side of the tape. 
2. finds the previous time the machine was at the left side of the tape. 
3. finds the maximum rightward displacement over that interval. 
4. if the leftmost bits of the tape are the same then and now, we have a proof!
5. (maybe future): check the condition again by brute force simulation
-}
attemptEndOfTapeProof :: SimOneAction
attemptEndOfTapeProof _machine state = assert (atLeftOfTape $ state ^. s_tape) $
    maybe (Right state) (Left . ContinueForever) maybeProof
 where
  samePhase = (== state ^. s_phase)
  samePoint (ExpTape _ls oldPoint _rs) = oldPoint == point (state ^. s_tape)
  isCandidate (phase, tape) = samePhase phase && atLeftOfTape tape && samePoint tape
  dispList = Unsafe.tail $ state ^. s_disp_history
  maximumInwardList = fmap maximum $ tail $ inits dispList
  bitsToCheck = uncurry (-) <$> zipExact maximumInwardList dispList
  candidates = filter (isCandidate . view _2) $ zipExact bitsToCheck $ Unsafe.tail $ state ^. s_history
  -- int is from bitsToCheck
  checkProof :: (Int, (Phase, ExpTape Bit InfCount)) -> Maybe HaltProof
  checkProof (numBitsToCheck, (_ph, oldTape)) = let
    getBits tapeHalf = takeExact numBitsToCheck $ tapeHalfToBitList tapeHalf <> repeat False
    in
    if getBits (right oldTape) == getBits (right $ state ^. s_tape)
      then Just $ OffToInfinityN (state ^. s_steps) L
      else Nothing
  maybeProof :: Maybe HaltProof
  maybeProof = viaNonEmpty head $ mapMaybe checkProof candidates


attemptOtherEndOfTapeProof :: SimOneAction
attemptOtherEndOfTapeProof _machine state = assert (atRightOfTape $ state ^. s_tape) $
    maybe (Right state) (Left . ContinueForever) maybeProof
 where
  samePhase = (== state ^. s_phase)
  samePoint (ExpTape _ls oldPoint _rs) = oldPoint == point (state ^. s_tape)
  isCandidate (phase, tape) = samePhase phase && atRightOfTape tape && samePoint tape
  dispList = Unsafe.tail $ state ^. s_disp_history
  minimumInwardList = fmap minimum $ tail $ inits dispList
  bitsToCheck = uncurry (-) <$> zipExact dispList minimumInwardList
  candidates = filter (isCandidate . view _2) $ zipExact bitsToCheck $ Unsafe.tail $ state ^. s_history
  -- int is from bitsToCheck
  checkProof :: (Int, (Phase, ExpTape Bit InfCount)) -> Maybe HaltProof
  checkProof (numBitsToCheck, (_ph, oldTape)) = let
    getBits tapeHalf = takeExact numBitsToCheck $ tapeHalfToBitList tapeHalf <> repeat False
    in
    if getBits (left oldTape) == getBits (left $ state ^. s_tape)
      then Just $ OffToInfinityN (state ^. s_steps) R
      else Nothing
  maybeProof :: Maybe HaltProof
  maybeProof = viaNonEmpty head $ mapMaybe checkProof candidates


loopSimulateSkip :: Int -> Turing -> OneLoopRes
loopSimulateSkip limit = simulateOneMachineOuterLoop $ pure $ simulateStepTotalLoop limit

indGuessLoop ::  Int -> Turing -> OneLoopRes
indGuessLoop limit = simulateOneMachineOuterLoop $
  simulateStepTotalLoop limit :| [liftModifyState recordHist, runAtCount 100 attemptInductionGuess]

simulateManyBasicLoop :: Int -> Turing -> [_]
simulateManyBasicLoop limit = simulateManyMachinesOuterLoop $ simulateStepPartial limit
  :| (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof
  ])

loopForEndOfTapeGlue :: Int -> Turing -> OneLoopRes
loopForEndOfTapeGlue limit = simulateOneMachineOuterLoop $
    simulateStepTotalLoop limit :| [liftModifyState recordHist, liftModifyState recordDispHist, runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof]

simulateForTime :: Int -> Turing -> OneLoopRes
simulateForTime time = simulateOneMachineOuterLoop actionList where
  actionList = simulateStepTotalLoop (time + 1) :| [liftModifyState recordHist]

getStateAfterTime :: Int -> Turing -> SimState
getStateAfterTime time turing = last $ simulateForTime time turing ^. _2

makeIndGuess :: Int -> Turing -> Maybe (Skip Bit)
makeIndGuess stepCount turing = guessInductionHypothesis histToUse where
  histToUse = reverse $ getStateAfterTime stepCount turing ^. s_history

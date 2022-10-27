module MoreSimulationLoops where

import Relude
import qualified Relude.Unsafe as Unsafe
import qualified Relude.Unsafe as U
import Control.Lens
import Prettyprinter
import Control.Exception (assert)

import qualified Data.Map as M
import qualified Data.Map.Monoidal as MM
import qualified Data.Set as S

import Turing ( fillInMachine, Bit, Phase, Turing )
import Count
import Results
import SimulateSkip
import Skip
import Induction
import SimulationLoops
import Util
import HaltProof
import LinRecurrence
import TapeSymbol
import SimulateTwoBit (TwoBit)
import ExpTape
import Scaffold
import Relude.Extra (bimapBoth)
import Safe.Exact

attemptInductionGuess :: Turing -> SimState Bit
  -> Either (SimResult InfCount Bit) (SimState Bit)
attemptInductionGuess machine state = trace "attempted" $
  case guessInductionHypothesis hist rsHist of
    Left msg -> traceShow msg $ Right state
    --try to prove the skip by induction 
    Right skip -> trace ("guessed a skip:\n" <> show (pretty skip)) $
      case proveInductively 20 machine (state ^. s_book) skip (BoundVar 0) of
        Left (fail, _config) -> trace (toString fail) $ Right state
        Right skipOrigin -> trace ("succeeded") $
          addSkipToStateOrInf skip skipOrigin state
  where
    hist =  state ^. s_history
    rsHist = state ^. s_readshift_history

--Note! this function is outdated
indGuessLoop ::  Int -> Turing -> OneLoopRes Bit
indGuessLoop limit = simOneFromStartLoop $
  simulateStepTotalLoop limit :| [liftModifyState recordHist,
   liftModifyState recordDispHist,
   runAtCount 100 attemptInductionGuess]

-- this function works though
makeIndGuess :: forall s. (TapeSymbol s) => Int -> Turing -> Either Text (Skip Count s)
makeIndGuess = uncurry guessInductionHypothesis .: getTwoHistAfterTime

getRecurRes :: Int -> Turing -> Maybe (HaltProof Bit)
getRecurRes stepCount turing = detectLinRecurrence tapeHist rsHist where
  tapeHist = guessingState ^. s_history
  rsHist = guessingState ^. s_readshift_history
  guessingState = getStateAfterTime stepCount turing

{-
plan for integrating proveInductivelyIMeanIT into the main loop:
we need to write a function which checks whether a skip goes forever in already known history
then we change the return type of proveInd to return the new skip if possible
then we write a function which runs proveInd, if it succeeds uses chainArbitrary, 
and then checks whether the skip runs forever
-}


proveByInd :: (TapeSymbol s) => SimOneAction s
proveByInd machine state = --force $ --trace ("proveByInd on:\n" <> showP machine) $ 
 case eTProof of
  Left _msg -> Right newState
  Right hp -> Left $ ContinueForever hp
  where
  hist = state ^. s_history
  rsHist =  state ^. s_readshift_history
  (newbook, eTSkip) = let ans = proveInductivelyIMeanIT machine (state ^. s_book) (state ^. s_steps) hist rsHist
    in
      --trace ("etskip:\n" <> showP (ans ^. _2)) 
      ans
  newState = state & s_book .~ newbook
  eTArbSkip = let ans = chainArbitrary =<< eTSkip in
    --trace ("etarbskip:\n" <> showP ans) 
    ans
  eTProof = let ans = flip skipAppliesForeverInHist hist =<< eTArbSkip in
    --trace ("etproof:\n" <> show ans) 
    ans
{-# SPECIALISE proveByInd :: SimOneAction Bit #-}
{-# SPECIALISE proveByInd :: SimOneAction TwoBit #-}


proveByIndV1 ::(TapeSymbol s) => SimOneAction s
proveByIndV1 machine state =
  case mbProof of
    Left _msg -> Right state
    Right hp -> Left $ ContinueForever hp
  where
    hist = state ^. s_history
    rsHist = state ^. s_readshift_history
    mbProof = do
      indGuess <- guessInductionHypothesis hist rsHist
      (scaffoldSkip, scaffoldOrigin) <-
       proveByScaffold machine (state ^. s_book) hist rsHist
      let newBook = addSkipToBook scaffoldSkip scaffoldOrigin (state ^. s_book)
      --this is where we obtain the skipOrigin that proves indGUess
      n <- --trace ("indguess: " <> showP indGuess <> "scaffoldSkip: " <> showP scaffoldSkip)
             --  <> "book: " <> showP (state ^. s_book))
           --this should really only be proveBySimulating, but the thing is, often you want to prove with
              --x, rather than with x+1, and proveInductively does that for you, which is helpful
        --first fst $ proveBySimulating 100 machine newBook indGuess
         first fst $ proveInductively 100 machine newBook indGuess (BoundVar 0)
      arbSkip <- chainArbitrary indGuess
      skipAppliesForeverInHist arbSkip hist

proveSimply :: (TapeSymbol s) => SimOneAction s
proveSimply machine state = case mbProof of
  Left txt -> trace (toString $ "provesimply failed because: " <> txt <> "\nEOM\n") $
    Right state
  Right hp -> Left $ ContinueForever hp
  where
  mbProof = do
    indHyp <- guessInductionHypothesis (state ^. s_history) (state ^. s_readshift_history)
    let tryProve skip = bimap fst (const skip) $
          proveSimLinearAndTree 100 100 machine (state ^. s_book) skip
        skipVar = case toList $ getAllVars indHyp of
          [x] -> x
          _ -> error "more than one var from indHyp"
    validSkip <- tryProve indHyp `alt` tryProve (add skipVar 1 indHyp) `alt` tryProve (add skipVar 2 indHyp)
    let mbProof1 = skipAppliesForeverInHist validSkip (state ^. s_history)
    let mbProof2 = do
          arbSkip <- first ("chainArbitrary failed: " <>) $ chainArbitrary validSkip
          skipAppliesForeverInHist arbSkip (state ^. s_history)
    mbProof1 `alt` mbProof2

  {-we need to try to prove the skip using (x+2) rather than (x) because sometimes you have to break
  the x into pieces to be able to prove it-}
  add var n skip = replaceVarInSkip skip var (FinCount n <> boundVarCount var 1)
{-# SPECIALISE proveSimply :: SimOneAction Bit #-}
{-# SPECIALISE proveSimply :: SimOneAction TwoBit #-}

alt :: Either Text a -> Either Text a -> Either Text a
alt l r = case (l, r) of
  (Right out, _) -> Right out
  (_, Right out) -> Right out
  (Left m1, Left m2) -> Left $ m1 <> "\nand\n" <> m2

{-
algorithm: for all configs which occur at least twice in the history of complexity at most 5:
find the last two times the config occured
create the rule that involves adding the differences 
  (you can add one thing to each edge, but at most 1)
try to prove that rule
if successful, then add the rule to the rulebook 
-}
addSinglePairRule :: forall s. (TapeSymbol s) => SimOneAction s
addSinglePairRule machine state = Right $ state & s_book .~ newBook where
  (TapeHist hist) = state ^. s_history
  (ReadShiftHist rsHist) = state ^. s_readshift_history
  book = state ^. s_book
  configs :: Set (Phase, Signature s)
  configs = fromList $ second tapeSignature <$> hist
  newSkips :: [(Skip Count s, SkipOrigin s)]
  newSkips = let ans = mapMaybe generalizeConfig $ toList configs in
    --trace ("new skips were: " <> foldMap showP (fst <$> ans))
    ans
  newBook = addChainedToBook $ addMultipleToBook newSkips book
  generalizeConfig :: (Phase, Signature s) -> Maybe (Skip Count s, SkipOrigin s)
  generalizeConfig (ph, sig) = case reverse $ filter (\(_i, (ph', tape)) -> (ph == ph') && sig == tapeSignature tape) $ zip [0, 1..] hist of
    [] -> Nothing
    [_] ->  Nothing
    revIndConfigs@((lastIndex, _lastConfig) : ((sndLastIndex, _sndLastConfig) : _rest)) ->
      do
        --we want the last two, the second-last-two and the first-two
      let configInds = fst <$> revIndConfigs
          possibleInds = firstTwo configInds : lastTwo configInds : maybeToList (secondLastTwo configInds)
      asum $ genFromIndices . swap <$> possibleInds
      where
      firstTwo (x : y : _) = (x, y)
      lastTwo (x : y : tail) = let
        ne1 = y :| tail
        (lastElm, rest) = (last ne1, init ne1)
        in (last (x :| rest), lastElm)
      secondLastTwo ([x, y]) = Nothing
      secondLastTwo (x : y : z : rest) = Just $ lastTwo $ init (x :| (y : z : rest))
      genFromIndices :: (Int, Int) -> Maybe (Skip Count s, SkipOrigin s)
      genFromIndices (genStart, genEnd) = do
          let (startTape, endTape) = getReadShiftSlicePair hist rsHist genStart genEnd
              (startSig, endSig) = (tapeSignature startTape, tapeSignature endTape)
          skip <- makeAdditiveSkip ph startTape endTape
          case proveSimLinearAndTree 100 100 machine book skip of
            Left _ -> Nothing
            Right numProveSteps -> Just (skip, PairGen sndLastIndex lastIndex numProveSteps)


makeAdditiveSkip :: (TapeSymbol s) => Phase
  -> ExpTape s Count -> ExpTape s Count
  -> Maybe (Skip Count s)
makeAdditiveSkip ph startTape endTape = do
  let (startSig, endSig) = (tapeSignature startTape, tapeSignature endTape)
  toDrop <- calcCommonSig startSig endSig
  let ((sCls, sCrs), (eCls, eCrs)) = addZeros toDrop $ bimapBoth getCounts (startTape, endTape)
      lrPairs = (zipExact sCls eCls, zipExact sCrs eCrs)
  genPairs <- bitraverseBoth (traverse genCountAdd) lrPairs
  --assembly from here is same as in guessInductionHypWithIndices
  pure $ assembleSkip genPairs ph (startSig, endSig)

genCountAdd :: (Count, Count) -> Maybe (Count, Count)
genCountAdd pair@(_, Empty) = Just pair
genCountAdd pair@(Empty, _) = Just pair
genCountAdd (FinCount n, FinCount m) = case compare n m of
  EQ -> Just (FinCount n, FinCount m)
  LT -> let
    diff = m - n
    bvc = boundVarCount (BoundVar 0) 1
    in
      Just (bvc, bvc <> FinCount diff)
  GT -> let
    diff = n - m
    bvc = boundVarCount (BoundVar 0) 1
    in 
      Just (bvc <> FinCount diff, bvc)
genCountAdd (_, _) = Nothing
{-
goal: write a function which runs 1) LR 2) cycle finding 3) end-of-tape
and checks that 1 iff (2 or 3)
it returns the LR proof if there is one, and it raises if the assert fails
-}

proveByLR :: (TapeSymbol s) => SimOneAction s
proveByLR _machine state = case maybeProof of
    Nothing -> Right state
    Just hp -> Left $ ContinueForever hp
  where
  maybeProof = detectLinRecurrence (state ^. s_history) (state ^. s_readshift_history)

{-# SPECIALISE proveByLR :: SimOneAction Bit #-}
{-# SPECIALISE proveByLR :: SimOneAction TwoBit #-}

proveLRLoop :: Int -> Turing -> OneLoopRes Bit
proveLRLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [liftModifyState recordHist, liftModifyState recordDispHist,
    runAtCount (limit-2) proveByLR]

canProveLR :: Int -> Turing -> Bool
canProveLR limit m = case proveLRLoop limit m of
  (ContinueForever (LinRecur {}), _ne) -> True
  (ContinueForever (SkippedToInfinity _), _ne) -> True
  _ -> False

fastLRLoop :: Int -> Turing -> OneLoopRes Bit 
fastLRLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit 
  :| [fastLRCheckAction] 

canProveFastLR :: Int -> Turing -> Bool 
canProveFastLR limit m = case fastLRLoop limit m of 
  (ContinueForever (LinRecur {}), _ne) -> True
  (ContinueForever (SkippedToInfinity _), _ne) -> True
  _ -> False

proveCycleLoop :: Int -> Turing -> OneLoopRes Bit
proveCycleLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [checkSeenBefore]

canProveCycle :: Int -> Turing -> Bool
canProveCycle limit m = case proveCycleLoop limit m of
  (ContinueForever (Cycle _ _), _ne) -> True
  (ContinueForever (SkippedToInfinity _), _ne) -> True
  _ -> False

proveEOTLoop :: Int -> Turing -> OneLoopRes Bit
proveEOTLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof]

canProveEOT :: Int -> Turing -> Bool
canProveEOT limit m = case proveEOTLoop limit m of
  (ContinueForever (LinRecur _ _ _), _) -> True
  (ContinueForever (OffToInfinityN _ _), _) -> True
  (ContinueForever (SkippedToInfinity _), _ne) -> True
  _ -> False

proveOEOTLoop :: Int -> Turing -> OneLoopRes Bit
proveOEOTLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof]

canProveOEOT :: Int -> Turing -> Bool
canProveOEOT limit m = case proveOEOTLoop limit m of
  (ContinueForever (LinRecur _ _ _), _) -> True
  (ContinueForever (OffToInfinityN _ _), _) -> True
  _ -> False

checkLRAssertOneMachine :: Int -> Turing -> Maybe Text
checkLRAssertOneMachine limit unfinishedM = if toAssert then Nothing else Just msg where
  m = fillInMachine unfinishedM
  lrWorked = canProveLR limit m
  cycleWorked = canProveCycle limit m
  eotWorked = canProveEOT limit m
  otherEotWorked = canProveOEOT limit m
  lrComplementsWorked = cycleWorked || eotWorked || otherEotWorked
  lrIffComplements = lrWorked == lrComplementsWorked
  toAssert = lrIffComplements
  msg = "assert failed on:\n" <> showP m
    <> " " <> showP [lrWorked, cycleWorked, eotWorked, otherEotWorked]

checkFastLRAssertOneMachine :: Int -> Turing -> Maybe Text 
checkFastLRAssertOneMachine limit unfinishedM = trace ("machine: " <> showP unfinishedM) $ if lrWorked == fastLRWorked then Nothing else
  Just msg where 
  m = fillInMachine unfinishedM
  lrWorked = canProveLR limit m 
  fastLRWorked = canProveFastLR (limit*2) m 
  msg = "m: " <> showP m <> "\nlrWorked: " <> show lrWorked <> " fastLRWorked: " <> show fastLRWorked

--todo run at count being measured in big steps while limit is measured in small steps is bad
indProveLoop :: Int -> Turing -> OneLoopRes Bit
indProveLoop limit = simOneFromStartLoop $ simulateStepTotalLoop limit
  :| [checkSeenBefore, liftModifyState recordHist, liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof,
  runAtCount 50 proveByInd
  ]


enumerateMachinesLoop :: Int -> Turing -> MultiLoopRes Bit
enumerateMachinesLoop limit = simulateManyMachinesOuterLoop (const Nothing) $
  simulateStepPartial limit :| []

checkLRAssertManyMachines :: Int -> Turing -> [Text]
checkLRAssertManyMachines limit startMachine = catMaybes texts where
  machines = fst <$> enumerateMachinesLoop limit startMachine
  texts = checkLRAssertOneMachine limit <$> machines

checkFastLRAssertManyMachines :: Int -> Turing -> [Text] 
checkFastLRAssertManyMachines limit startMachine = catMaybes texts where
  machines = fst <$> enumerateMachinesLoop limit startMachine
  texts = checkFastLRAssertOneMachine limit <$> machines

indProveLoopMany :: Int -> Turing -> MultiLoopRes Bit
indProveLoopMany limit = simulateManyMachinesOuterLoop backwardSearch $
  simulateStepPartial limit :| (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist,
  liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof,
  runAtCounts [40, 140] proveByInd
  ])

bestCurrentProveLoop :: Int -> Turing -> MultiLoopRes Bit
bestCurrentProveLoop limit = simulateManyMachinesOuterLoop backwardSearch $
  simulateStepPartial limit :| (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist,
  liftModifyState recordDispHist,
  runAtCounts [10, 40, 140] proveByLR,
  runAtCounts [40, 140] proveByInd
  ])

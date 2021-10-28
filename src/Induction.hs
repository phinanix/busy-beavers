module Induction where

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)
import qualified Data.Map as M
import qualified Data.Text as T (concat)
import Prettyprinter

import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
    ( SkipBook,
      SkipOrigin(Induction),
      PartialStepResult(Stepped, Unknown, Stopped, MachineStuck),
      skipStep )
import Data.Bits (Bits(bit))
import Data.List (minimumBy)
import Relude.Extra (bimapBoth)
import Relude.Foldable (Bitraversable)
import Safe.Exact
import Control.Exception (assert)
import Data.Foldable
import Relude.Unsafe ((!!))
import qualified Relude.Unsafe as U

--goal: make a thing that takes a skip that might apply to a certain machine, 
--attempts to simulate forward to prove that skip using induction
-- the first int is the limit on the number of steps to take before giving up 
--the (skip bit) input is the goal to be proven, 
-- the BoundVar is the variable on which we are going to do induction
--returns Left with an error message 
--or Right with success
proveInductively :: Int -> Turing -> SkipBook Bit -> Skip Bit -> BoundVar -> Either Text (SkipOrigin Bit)
proveInductively limit t book goal indVar = case baseCase of
    Left m -> Left $ "failed base: " <> m
    Right _ -> case indCase of
        Left m -> Left $ "failed ind: " <> m
        Right _ ->  pure origin
    where
    origin :: SkipOrigin Bit
    origin = Induction book limit
    baseCase :: Either Text Count
    baseCase = proveBySimulating limit t book baseGoal
    baseGoal :: Skip Bit
    baseGoal = replaceVarInSkip goal indVar $ finiteCount 1
    indCase :: Either Text Count
    indCase = proveBySimulating limit t book indGoal
    indGoal :: Skip Bit
    indGoal = replaceVarInSkip goal indVar $ symbolVarCount newSymbolVar 1
    newSymbolVar :: SymbolVar --TODO: this is obviously incredibly unsafe
    newSymbolVar = SymbolVar 4

-- given a skip, replaces all occurences of a particular BoundVar with a particular Count
replaceVarInSkip :: Skip s -> BoundVar -> Count -> Skip s
replaceVarInSkip (Skip sConfig eSE hopCount halts displacement) varIn countOut =
    Skip newConfig newSE (replaceVarInCount hopCount) halts (replaceVarInDisplacement displacement) where
    newConfig = replaceVarInConfig sConfig
    newSE = replaceVarInSE eSE
    replaceVarInConfig (Config p ls c_point rs)
        = Config p
        (replaceVarInList ls)
        c_point
        (replaceVarInList rs)
    replaceVarInSE = \case
        EndMiddle config -> EndMiddle $ replaceVarInConfig config
        EndSide p d xs -> EndSide p d $ replaceVarInList xs
    replaceVarInDisplacement = \case
        Zero -> Zero
        OneDir d c -> OneDir d $ replaceVarInCount c
        BothDirs c c' -> BothDirs (replaceVarInCount c) (replaceVarInCount c')
    replaceVarInList :: [(s, Count)] -> [(s, Count)]
    replaceVarInList = fmap $ fmap replaceVarInCount
    replaceVarInCount :: Count -> Count
    replaceVarInCount (Count num symbolMap boundMap) =
        Count num symbolMap Empty <> foldMap updateVar (assocs boundMap) where
            updateVar (v, Sum n) = if v == varIn
                then n `nTimes` countOut
                else boundVarCount v n

-- input int is limit on number of steps to simulate
-- output count is the number of steps it actually took 
proveBySimulating :: Int -> Turing -> SkipBook Bit -> Skip Bit -> Either Text Count
proveBySimulating limit t book (Skip start goal _ _ _)
    = loop 0
    (start ^. cstate)
    (second NotInfinity $ configToET start ^. _2)
    (finiteCount 0)
    where
    -- four conditions: we've taken more steps than the limit,
    -- we've succeeded, stepping fails for some reason, or we continue 
    loop :: Int -> Phase -> ExpTape Bit InfCount -> Count -> Either Text Count
    loop numSteps p tape curCount
      |indMatch p tape goal = pure curCount
      | numSteps > limit = Left "exceeded limit while simulating"
      | otherwise = case skipStep t book p tape of
            Unknown e -> Left $ "hit unknown edge" <> show e
            Stopped {} -> Left "halted while simulating"
            MachineStuck -> Left $ "machine stuck in phase:" <> show p
                <> "\ngoal:" <> show (pretty goal) <> "\ncur tape:" <> dispExpTape tape
            Stepped Infinity _ _ _ _ -> Left "hopped to infinity"
            Stepped (NotInfinity hopsTaken) newPhase newTape _ _
                -> loop (numSteps + 1) newPhase newTape (curCount <> hopsTaken)
    indMatch :: Phase -> ExpTape Bit InfCount -> SkipEnd Bit -> Bool
    indMatch cur_p et se = case bitraverse pure deInfCount et of
        Nothing -> False
        Just tape@(ExpTape ls point rs) -> case se of
            EndMiddle (Config ph c_ls c_p c_rs)
                -> cur_p == ph && ls == c_ls && point == c_p && rs == c_rs
            EndSide goalPhase dir xs -> endSideTapeMatch dir xs tape &&
                endSideTransMatch dir goalPhase t cur_p tape
      where
        endSideTapeMatch :: Dir -> [(Bit, Count)] -> ExpTape Bit Count -> Bool
        endSideTapeMatch L goal (ExpTape _ls point rs) = case getNewFinPoint goal of
            Nothing -> False
            Just (goal_p, goal_xs) -> goal_p == point && goal_xs == rs --yes this is reversed
        endSideTapeMatch R goal (ExpTape ls point _rs) = case getNewFinPoint goal of
            Nothing -> False
            Just (goal_p, goal_xs) -> goal_p == point && goal_xs == ls --yes this is reversed
        endSideTransMatch :: Dir -> Phase -> Turing -> Phase ->  ExpTape Bit Count -> Bool
        endSideTransMatch goal_d goalPhase (Turing _n map) curPhase (ExpTape _ p _)
            = case map ^. at (curPhase, p) of
                Nothing -> False
                (Just Halt) -> goal_d == L
                (Just (Step transPhase _bit d)) -> goal_d == d && goalPhase == transPhase
        deInfCount Infinity = Nothing
        deInfCount (NotInfinity c) = Just c

--this is wrong, it needs to be ziplist-y
transposeNE :: NonEmpty [a] -> [NonEmpty a]
transposeNE (x :| xs) = getZipList $ (:|) <$> ZipList x <*> ZipList (transpose xs)

bitraverseBoth :: (Bitraversable p, Applicative f) => (a -> f b) -> p a a -> f (p b b)
bitraverseBoth f = bitraverse f f

list1AllEqual :: (Ord a) => NonEmpty a -> Bool
list1AllEqual (x :| rest) = all (== x) rest

boolToMaybe :: Bool -> Maybe ()
boolToMaybe True = Just ()
boolToMaybe False = Nothing

mNEToList :: Maybe (NonEmpty a) -> [a]
mNEToList Nothing = []
mNEToList (Just ne) = toList ne

showEval :: (Show a) => a -> a
showEval x = traceShow x x

showEvalN :: Show a => String -> a -> a
showEvalN t x = trace (t <> "\n" <> show x) x

showTapePhaseList :: [(Phase, ExpTape Bit InfCount)] -> String
showTapePhaseList tapes = toString $ T.concat $ (\(p, x) -> dispPhase p <> " " <> dispExpTape x <> "\n") <$> tapes

--given a history, guesses a "critical configuration" 
-- a simple tape appearance the machine repeatedly returns to
guessCriticalConfiguration :: [(Phase, ExpTape Bit InfCount)] -> (Phase, Signature Bit)
guessCriticalConfiguration hist = minimumBy (compare `on` signatureComplexity . snd) possibleSigs where
    tapeSignatures :: [(Phase, Signature Bit)]
    tapeSignatures = tapeSignature <$$> hist
    sigFreqs :: Map (Phase, Signature Bit) Int
    sigFreqs = M.fromListWith (+) $ (,1) <$> tapeSignatures
    possibleSigs :: [(Phase, Signature Bit)]
    possibleSigs = filter (\s -> sigFreqs ^?! ix s >= 3) tapeSignatures

-- given a particular config, return the list of times that config occurred, plus the integer position in the original list
obtainConfigIndices :: [(Phase, ExpTape Bit InfCount)] -> (Phase, Signature Bit)
    -> [(Int, (Phase, ExpTape Bit InfCount))]
obtainConfigIndices hist config
    = filter (\(_, (p, tape)) -> (p, tapeSignature tape) == config) $ zip [0, 1 .. ] hist

--given a list of displacements and a start and end index, return the maximum 
--left and rightward displacements that occured between the two indices, inclusive 
maximumDisplacement :: [Int] -> Int -> Int -> (Int, Int)
maximumDisplacement ds start end = let d_len = length ds in
  assert (start <= end && start <= d_len && end <= d_len)
  (minimum portion, maximum portion) where
    portion = slice start end ds

--given a tape history, a history of (relative) displacement, and a start and end point
--obtain a slice of tape corresponding to everything the machine read / output at the start 
--and end points respectively
getSlicePair :: [(Phase, ExpTape Bit InfCount)] -> [Int] -> Int -> Int -> (ExpTape Bit Count, ExpTape Bit Count)
getSlicePair hist disps start end = (startSlice, endSlice) where
    startDisp = disps !! start
    endDisp = disps !! end
    (leftAbsDisp, rightAbsDisp) = maximumDisplacement disps start end
    --to get the left and right displacements relative to a particular position (ie the start or end)
    -- you have to subtract off that position, so it becomes zero, and the other ones become relative
    startSlice = sliceExpTape (hist ^?! ix start . _2) (leftAbsDisp - startDisp) (rightAbsDisp - startDisp)
    endSlice = sliceExpTape (hist ^?! ix end . _2) (leftAbsDisp - endDisp) (rightAbsDisp - endDisp)

--says whether by dropping one or both the left or the right bits of the start sig, we can reach the end sig
commonSig :: Signature Bit -> Signature Bit -> Maybe (Bool, Bool)
commonSig start end = asum $ check <$> tf <*> tf where
    tf = [False, True]
    check dl dr = let
      lFunc = if dl then dropLeft else id
      rFunc = if dr then dropRight else id
      in if lFunc (rFunc start) == end then Just (dl, dr) else Nothing
    dropLeft (Signature ls p rs) = Signature (U.init ls) p rs
    dropRight (Signature ls p rs) = Signature ls p (U.init rs)

--if we have to drop one or both of of the end bits of the start signature, then to compensate we will add
--a zero to the end signature in the places we drop the bits 
addZeros :: (Bool, Bool) -> ([Count], [Count]) -> ([Count], [Count])
addZeros (dl, dr) (ls, rs) = (lFunc ls, rFunc rs) where
    appendZero xs = xs <> [Empty]
    lFunc = if dl then appendZero else id
    rFunc = if dr then appendZero else id

guessInductionHypothesis2 :: [(Phase, ExpTape Bit InfCount)] ->[Int] -> Maybe (Skip Bit)
guessInductionHypothesis2 hist disps = do
  let
    criticalConfig = guessCriticalConfiguration hist
    configIndicesAndConfigs = obtainConfigIndices hist criticalConfig
    configIndices = fst <$> configIndicesAndConfigs
    indexPairs = zipExact (U.init configIndices) (U.tail configIndices)
    slicePairs = uncurry (getSlicePair hist disps) <$> indexPairs
    allSigs = fmap (bimapBoth tapeSignature) slicePairs
  --only proceed from here if all the pairs have the same signature at both the start and the end
  guard (allEqual allSigs)
  --to finish from here, our goal is for each transition start -> end, make a bunch of pairs of counts 
  --and then to generalize those pairs of counts accross all the transitions
  --to do this, we have to find a "common signature" for the start and end - we have allowed them to be 
  --different for the moment
  toDrop <- uncurry commonSig =<< viaNonEmpty head allSigs
  let
    countListPairPairs :: [(([Count], [Count]), ([Count], [Count]))]
    countListPairPairs = bimapBoth getCounts <$> slicePairs
    --fmap over the list, then use second to only add zeros to the end signatures
    augCountPairPairs = fmap (second (addZeros toDrop)) countListPairPairs 
    doubleZipExact :: (([a], [x]), ([b], [y])) -> ([(a, b)], [(x, y)])
    doubleZipExact ((as, xs), (bs, ys)) = (zipExact as bs, zipExact xs ys)
    countPairListList :: [([(Count, Count)], [(Count, Count)])]
    countPairListList = doubleZipExact <$> augCountPairPairs 
    -- the previous list's first index is over different times the critical config occured 
    -- pair index is over left or right, and then third index is over the signature length
    -- we want the outer index to be the pair, then the signature legnth index, then the 
    -- occurence index that was originally first
    transposePairs :: [([a], [b])] -> ([[a]], [[b]])
    transposePairs pairs = bimap transpose transpose (fst <$> pairs, snd <$> pairs)
  thingsToGeneralizeList <- bitraverseBoth (traverse nonEmpty) $ transposePairs countPairListList 
  allThingsGeneralized <- bitraverseBoth (traverse generalizeFromCounts) thingsToGeneralizeList
  --finishing from here is just munging - we have the common signature (almost), we have the common count 
  --pairlists, we just need to assemble them all into the skip of our dreams

  Nothing

-- TODO: write a function that guesses a good induction hypothesis given a history of the tape 
-- (first guess: the simplest signature that has occurred 3 times, guess the additive induction if one exists)
guessInductionHypothesis :: [(Phase, ExpTape Bit InfCount)] -> Maybe (Skip Bit)
guessInductionHypothesis tapesAndPhases = skipOut where
    simplestSig = guessCriticalConfiguration tapesAndPhases
    goalTapes :: Maybe (NonEmpty (Phase, ExpTape Bit InfCount))
    goalTapes = let ans = nonEmpty $ filter (\(p, tape) -> (p, tapeSignature tape) == simplestSig) tapesAndPhases in
        trace ("goal:\n" <> showTapePhaseList (mNEToList ans)) ans
    --To complete this function, given the goal tapes, for each position, accumulate the counts at that position
    --a list of counts leads to a generalized guess for the overall (more complex) count, eg 1, 2, 3, leads to n, and 2,4,6 leads to 2n
    -- then you need to be able to union counts somehow maybe? or no, I think that's just it
    etToCounts (ExpTape ls _p rs) = (snd <$> ls, snd <$> rs)
    -- appears correct
    countOfGoalTapes :: Maybe (NonEmpty ([InfCount], [InfCount]))
    countOfGoalTapes = showEvalN "countOfGoalTapes" $ etToCounts . snd <$$> goalTapes
    -- appears correct
    pairOfCountLists :: Maybe ([NonEmpty InfCount], [NonEmpty InfCount])
    pairOfCountLists = showEvalN "pairOfCountLists" $ bisequence (transposeNE <$> (fst <$$> countOfGoalTapes),
                                   transposeNE <$> (snd <$$> countOfGoalTapes))
    pairUpNe :: NonEmpty a -> [(a, a)]
    pairUpNe xs = zipExact (init xs) (tail xs)
    pairOfCountPairs :: Maybe ([NonEmpty (InfCount, InfCount)], [NonEmpty (InfCount, InfCount)])
    pairOfCountPairs = showEvalN "pairOfCountPairs" $ bimapBoth (fmap $ fromList . pairUpNe) <$> pairOfCountLists
    allCountsGeneralizedEither :: Maybe ([Either () (Count, Count)], [Either () (Count, Count)])
    allCountsGeneralizedEither = bitraverseBoth (traverse generalizeFromInfCounts) =<< pairOfCountPairs
    goalPoints :: Maybe (NonEmpty Bit)
    goalPoints = point . snd <$$> goalTapes
    targetPoint :: Maybe Bit
    targetPoint = head <$> goalPoints
    etPointsStacked :: Maybe Bit --really worried I got this one wrong -- 23:50 29Sep21
    etPointsStacked = (boolToMaybe . list1AllEqual =<< goalPoints) >> targetPoint
    mungePairedStuff :: ((Count, Count) -> Count) -> [(Bit, Either () (Count, Count))] -> Maybe [(Bit, Count)]
    mungePairedStuff f = \case
        [] -> Just []
        [(False, eitherUnitPair)] -> case eitherUnitPair of
            Left () -> Just []
            Right cPair -> Just [(False, f cPair)]
        (b, eitherUnitPair) : rest -> case eitherUnitPair of
            Left () -> Nothing
            Right cPair -> (:) (b, f cPair) <$> mungePairedStuff f rest

    skipOut = do
        (lPairs, rPairs) <- allCountsGeneralizedEither
        point <- etPointsStacked
        actualGoalTapes <- goalTapes
        let targetPhase = fst $ head actualGoalTapes
        goalPhase <- boolToMaybe (list1AllEqual $ fst <$> actualGoalTapes) $> targetPhase
        let (Signature lSig p rSig) = tapeSignature . snd . head $ actualGoalTapes
        if p /= point then error "oh no skipOut" else Just ()
        let
         makeConfig f = do
             lStuff <- mungePairedStuff f $ zipExact lSig lPairs
             rStuff <- mungePairedStuff f $ zipExact rSig rPairs
             pure $ Config goalPhase lStuff p rStuff
        startConfig <- makeConfig fst
        endConfig <- makeConfig snd
        --todo - the zeros for steps and displacement are placeholders
        pure $ Skip startConfig (EndMiddle endConfig) (finiteCount 0) False Zero

--takes a list of at least 2 pairs of counts, and returns a pair of counts that generalizes them,
-- if possible, in the sense that it has bound vars which can be subbed to be all the pairs
--algorithm: if each pair is equal, return said pair
-- else, if they share a common integer difference, return the function that applies that difference 
-- such as n + 2 -> n, or n -> n + 3
-- else, see if they are generated by a function of the form x -> m * x + b 
-- else give up 
generalizeFromCounts :: NonEmpty (Count, Count) -> Maybe (Count, Count)
generalizeFromCounts xs = allEqualPair <|> additivePair <|> affinePair where
    allEqualPair :: Maybe (Count, Count)
    allEqualPair = guard (list1AllEqual xs) >> pure (head xs)
    countToMaybeNat = \case
        Count n Empty Empty -> Just n
        _ -> Nothing
    naturalPairs :: Maybe (NonEmpty (Natural, Natural))
    naturalPairs = let ans = traverse (bitraverse countToMaybeNat countToMaybeNat) xs in
        traceShow ans ans
    subNats :: Natural -> Natural -> Int
    subNats = (-) `on` fromIntegral
    differences = uncurry subNats <$$> naturalPairs
    newBoundVarBad :: Count
    newBoundVarBad = newBoundVar 0
    --takes an integer and returns the count pair that represents a function that adds that to its input
    generalizeAddDiff :: Int -> (Count, Count)
    generalizeAddDiff d = case compare d 0 of
        --this means (x, y) x > y since d = x - y
        GT -> (newBoundVarBad <> finiteCount (fromIntegral d), newBoundVarBad)
        --this means (x, y) x < y
        LT -> (newBoundVarBad, newBoundVarBad <> finiteCount (fromIntegral $ -1 * d))
        EQ -> error "generalizeAddDiff should not be called on a zero integer"
    additivePair :: Maybe (Count, Count)
    additivePair = differences >>= \case
        ds@(d1 :| _rest) -> guard (list1AllEqual ds) >> pure (generalizeAddDiff d1)
    conformsToAffine :: Natural -> Int -> (Natural, Natural) -> Bool
    conformsToAffine m b (x, y) = fromIntegral x * fromIntegral m + b == fromIntegral y
    generalizeMulDiff :: Natural -> Int -> (Count, Count)
    generalizeMulDiff m b =  if b >= 0
        then (newBoundVarBad, m `nTimes` newBoundVarBad <> finiteCount (fromIntegral b))
        else (newBoundVarBad <> finiteCount (fromIntegral $ -1 * b), m `nTimes` newBoundVarBad)
    affinePair :: Maybe (Count, Count)
    affinePair = naturalPairs >>= \case
        (_pair :| []) -> Nothing
        --going for x -> m * x + b - we assume m > 0 but b can be any integer
        -- does not handle x -> m * (x + a) + b - but probably could somehow?
        pairs@((x1, y1) :| (x2, y2) : _rest) -> do
            m <- if y2 >= y1
                    --TODO :: this crashes if x1 == x2
                    then (y2 - y1) `maybeDiv` (x2 - x1)
                    else (y1 - y2) `maybeDiv` (x1 - x2)
            let b :: Int = fromIntegral y1 - fromIntegral m * fromIntegral x1
            guard $ all (conformsToAffine m b) pairs
            pure $ generalizeMulDiff m b

--returns Nothing if generalizing fails, Left () if generalizing succeeds because they are all infinity
--or Right (pair) if generlizing succeeds because none are infinity and generalizing count pairs succeeds
generalizeFromInfCounts :: NonEmpty (InfCount, InfCount) -> Maybe (Either () (Count, Count))
generalizeFromInfCounts xs = infinityUnit <|> notInfinityCountPair where
    infinityUnit :: Maybe (Either () (Count, Count))
    infinityUnit = guard (all (uncurry ((&&) `on` (== Infinity))) xs) >> pure (Left ())
    notInfinityCountPair :: Maybe (Either () (Count, Count))
    notInfinityCountPair = Right <$> (maybeAllCounts >>= generalizeFromCounts)
    infCountToMaybeCount :: InfCount -> Maybe Count
    infCountToMaybeCount = \case
        Infinity -> Nothing
        NotInfinity c -> Just c
    maybeAllCounts :: Maybe (NonEmpty (Count, Count))
    maybeAllCounts = traverse (bitraverse infCountToMaybeCount infCountToMaybeCount) xs
    packageResult :: Either () (Count, Count) -> (InfCount, InfCount)
    packageResult (Left ()) = (Infinity, Infinity)
    packageResult (Right tup) = bimapBoth NotInfinity tup

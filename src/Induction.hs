module Induction where

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter

import Data.Bits (Bits(bit))
import Data.List (minimumBy, findIndex)
import Relude.Extra (bimapBoth)
import Relude.Foldable (Bitraversable)
import qualified Relude.Unsafe as Unsafe
import Safe.Exact
import Control.Exception (assert)
import Data.Foldable
import Relude.Unsafe ((!!))
import qualified Relude.Unsafe as U

import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
import SimulationLoops
import Display
import Safe.Partial

--goal: make a thing that takes a skip that might apply to a certain machine, 
--attempts to simulate forward to prove that skip using induction
-- the first int is the limit on the number of steps to take before giving up 
--the (skip bit) input is the goal to be proven, 
-- the BoundVar is the variable on which we are going to do induction
--returns Left with an error message 
--or Right with success
proveInductively :: Int -> Turing -> SkipBook Bit -> Skip Count Bit -> BoundVar -> Either Text (SkipOrigin Bit)
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
    baseGoal :: Skip Count Bit
    baseGoal = replaceVarInSkip goal indVar $ finiteCount 1
    goalPlusX x = replaceVarInSkip goal indVar $ FinCount x <> symbolVarCount newSymbolVar 1
    indCase :: Either Text Count
    --this doesn't actually add the inductive hypothesis to the book!
    indCase = trace "\n\nstarting ind\n\n\n\n" $ deepseq indHyp $
        proveBySimulating limit t 
         (addSkipToBook (goalPlusX 0) InductionHypothesis $ addSkipToBook indHyp InductionHypothesis book) 
         indGoal
    indHyp :: Skip Count Bit 
    indHyp = let 
        ans = goalPlusX 1 
        msg = "indHyp is:\n" <> show (pretty ans)
      in 
        force $ trace msg ans
    indGoal :: Skip Count Bit
    indGoal = goalPlusX 2 
    newSymbolVar :: SymbolVar --TODO: this is obviously incredibly unsafe
    newSymbolVar = SymbolVar 4

-- given a skip, replaces all occurences of a particular BoundVar with a particular Count
replaceVarInSkip :: Skip Count s -> BoundVar -> Count -> Skip Count s
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
proveBySimulating :: Int -> Turing -> SkipBook Bit -> Skip Count Bit -> Either Text Count
proveBySimulating limit t book (Skip start goal _ _ _)
    = trace ("starting pos:\n" <> show (pretty start) <> "\n") $ loop 0
    (start ^. cstate)
    (second NotInfinity $ configToET start ^. _2)
    (finiteCount 0)
    where
    -- four conditions: we've taken more steps than the limit,
    -- we've succeeded, stepping fails for some reason, or we continue 
    loop :: Int -> Phase -> ExpTape Bit InfCount -> Count -> Either Text Count
    loop numSteps p tape curCount
      | trace (toString $ "p:" <> dispPhase p <> " tape is: " <> dispExpTapeIC tape) False = undefined
      |indMatch p tape goal = pure curCount
      | numSteps > limit = Left "exceeded limit while simulating"
      | otherwise = case skipStep t book p tape of
            Unknown e -> Left $ "hit unknown edge" <> show e
            Stopped {} -> Left "halted while simulating"
            MachineStuck -> Left $ "machine stuck on step: " <> show numSteps
                <> " in phase:" <> show p
                <> "\ngoal:" <> show (pretty goal) <> "\ncur tape:" <> dispExpTapeIC tape
            Stepped Infinity _ _ _ _ -> Left "hopped to infinity"
            Stepped (NotInfinity hopsTaken) newPhase newTape _ _
                -> loop (numSteps + 1) newPhase newTape (curCount <> hopsTaken)
    indMatch :: Phase -> ExpTape Bit InfCount -> SkipEnd Count Bit -> Bool
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
showTapePhaseList tapes = toString $ T.concat $ (\(p, x) -> dispPhase p <> " " <> dispExpTapeIC x <> "\n") <$> tapes

possibleSignatures :: [(Phase, ExpTape Bit InfCount)] -> [(Phase, Signature Bit)]
possibleSignatures hist = filter (\s -> sigFreqs ^?! ix s >= 3) tapeSignatures where
    tapeSignatures :: [(Phase, Signature Bit)]
    tapeSignatures = tapeSignature <$$> hist
    sigFreqs :: Map (Phase, Signature Bit) Int
    sigFreqs = M.fromListWith (+) $ (,1) <$> tapeSignatures

simplestNSigs :: Natural -> [(Phase, ExpTape Bit InfCount)] -> [(Phase, Signature Bit)]
simplestNSigs n hist = take (fromIntegral n) $
    sortBy (compare `on` signatureComplexity . snd) $
    possibleSignatures hist

--given a history, guesses a "critical configuration" 
-- a simple tape appearance the machine repeatedly returns to
guessCriticalConfiguration :: [(Phase, ExpTape Bit InfCount)] -> (Phase, Signature Bit)
guessCriticalConfiguration = minimumBy (compare `on` signatureComplexity . snd) . possibleSignatures

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

getSlicePair'' :: Partial
  => ExpTape Bit Count
  -> ExpTape Bit Count
  -> [Int] -> Int -> Int
  -> (ExpTape Bit Count, ExpTape Bit Count)
getSlicePair'' sT eT = getSlicePair' (second NotInfinity sT) (second NotInfinity eT)

getSlicePair' :: Partial 
  => ExpTape Bit InfCount
  -> ExpTape Bit InfCount
  -> [Int] -> Int -> Int
    -> (ExpTape Bit Count, ExpTape Bit Count)
getSlicePair' startTape endTape disps start end = (startSlice, endSlice) where
    startDisp = disps !! start
    endDisp = disps !! end
    (leftAbsDisp, rightAbsDisp) = maximumDisplacement disps start end
    --to get the left and right displacements relative to a particular position (ie the start or end)
    -- you have to subtract off that position, so it becomes zero, and the other ones become relative
    startSlice = sliceExpTape startTape (leftAbsDisp - startDisp) (rightAbsDisp - startDisp)
    endSlice = sliceExpTape endTape (leftAbsDisp - endDisp) (rightAbsDisp - endDisp)

--given a tape history, a history of (relative) displacement, and a start and end point
--obtain a slice of tape corresponding to everything the machine read / output at the start 
--and end points respectively
getSlicePair :: [(Phase, ExpTape Bit InfCount)] -> [Int] -> Int -> Int -> (ExpTape Bit Count, ExpTape Bit Count)
getSlicePair hist disps start end = getSlicePair' startTape endTape disps start end where
    startTape = hist ^?! ix start . _2
    endTape = hist ^?! ix end . _2

getSlicePairC :: [(Phase, ExpTape Bit Count)] -> [Int] -> Int -> Int -> (ExpTape Bit Count, ExpTape Bit Count)
getSlicePairC hist = getSlicePair $ (fmap $ fmap $ second NotInfinity) hist

--says whether by dropping one or both the left or the right bits of the start sig, we can reach the end sig
calcCommonSig :: Signature Bit -> Signature Bit -> Maybe (Bool, Bool)
calcCommonSig start end = asum $ check <$> tf <*> tf where
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

--I have no idea how to write this function
generalizeFromExamples :: [(ExpTape Bit Count, ExpTape Bit Count)] -> Maybe (Skip Count Bit)
generalizeFromExamples slicePairs = undefined

guessInductionHypothesis :: [(Phase, ExpTape Bit InfCount)] -> [Int] -> Maybe (Skip Count Bit)
guessInductionHypothesis hist disps = do
  let
    criticalConfig@(criticalPhase, _criticalSignature) = guessCriticalConfiguration hist
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
  (startSig, endSig) <- viaNonEmpty head allSigs
  toDrop <- calcCommonSig startSig endSig
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
  --the pair here is over left and right, then the list is over the "signature dimension", and the internal
  --pair is over start -> finish
  allThingsGeneralized <- bitraverseBoth (traverse generalizeFromCounts) thingsToGeneralizeList
  --we want to pull the pair from start -> finish out to the front, then have the left right pair, then have the 
  --"signature dimension"
  let startCounts = bimapBoth (fmap fst) allThingsGeneralized
      endCounts =  bimapBoth (fmap snd) allThingsGeneralized
      startConfig = combineIntoConfig criticalPhase startCounts startSig
      endConfig = combineIntoConfig criticalPhase endCounts endSig
  pure $ Skip startConfig (EndMiddle endConfig) Empty False Zero
  --finishing from here is just munging - we have the common signature (almost), we have the common count 
  --pairlists, we just need to assemble them all into the skip of our dreams
  where
  combineIntoConfig :: Phase -> ([Count], [Count]) -> Signature Bit -> Config Count Bit
  combineIntoConfig phase (leftCounts, rightCounts) (Signature leftBits p rightBits) =
    Config phase (zipExact leftBits (deleteZerosAtEnd leftCounts)) p
        (zipExact rightBits (deleteZerosAtEnd rightCounts))
  deleteZerosAtEnd :: [Count] -> [Count]
  deleteZerosAtEnd = \case
    [] -> []
    xs@(Empty : _rest) -> assert (allEqual xs) []
    notEmpty : rest -> notEmpty : deleteZerosAtEnd rest


timesSimplestNOccured :: Natural -> [(Phase, ExpTape Bit InfCount)] -> [Int]
timesSimplestNOccured n hist = sort $ fst <$> (obtainConfigIndices hist =<< simplestN) where
    simplestN = simplestNSigs n hist

simplestNExamples :: Natural -> [(Phase, ExpTape Bit InfCount)] -> [Int] -> [(ExpTape Bit Count, ExpTape Bit Count)]
simplestNExamples n hist disps = uncurry (getSlicePair hist disps) <$> increasingIndPairs where
    inds = timesSimplestNOccured n hist
    increasingIndPairs :: [(Int, Int)]
    increasingIndPairs = filter (uncurry (<)) $ (,) <$> inds <*> inds

zipSigToET :: Signature b -> ([c], [c]) -> ExpTape b c
zipSigToET (Signature b_ls p b_rs) (c_ls, c_rs) = ExpTape (zipExact b_ls c_ls) p (zipExact b_rs c_rs)

--gets the simulation history and the displacement history
--normally these are output backwards which is of course crazy so we fix them here 
simForStepNumFromConfig :: Int -> Turing -> Config Count Bit -> ([(Phase, ExpTape Bit Count)], [Int])
simForStepNumFromConfig limit machine startConfig
    = (reverse $ second deInfCount <$$> finalState ^. s_history, reverse $ finalState ^. s_disp_history)
    where
    (startPh, startTape) = second (second NotInfinity) $ configToET startConfig
    actionList = simulateStepTotalLoop limit :| [liftModifyState recordHist, liftModifyState recordDispHist]
    res = simulateOneMachineOuterLoop actionList machine (skipStateFromPhTape machine startPh startTape)
    finalState = last $ snd res

replaceSymbolVarInConfig :: Config Count s -> SymbolVar -> Count -> Config Count s
replaceSymbolVarInConfig config sv ans
    = first replaceSymbolVarInCount config where
        replaceSymbolVarInCount :: Count -> Count
        replaceSymbolVarInCount (Count n as xs) = Count n Empty xs <> foldMap updateVar (assocs as) where
            updateVar (v, Sum n) = if v == sv then n `nTimes` ans else symbolVarCount v n

{-takes in a machine, a tape configuration, and a symbolvar present in that tape configuration 
to generalize over. attempts to generate a skip with that config as a starting point
algorithm: instatiate the variable at several values, simulate forward a bunch of steps
take all signatures that occurred in each simulation, and try to generalize accross them, 
starting with the simplest first (eg, if 010 occurred many times, try to guess the function that
generates the coefficients of 0 1 and 0 from the instantiated symbolvar) 

right now generalizeFromCounts returns always (BoundVar 0), so as a hack we're going to change 
the symbolvar in the input config to be (BoundVar 0) also so it is the same

a lot of the possible "guesswhathappensnext"s are true but are once again not proveable via weak induction, so 
we're going to return a list of them instead, in the hopes that one works
for now, lets do all of the ones that have the same signature complexity as the minimum
-}
guessWhatHappensNext :: Turing -> Config Count Bit -> SymbolVar -> Maybe (Skip Count Bit)
guessWhatHappensNext machine config varToGeneralize
 = asum (generalizeOneSig <$> sortOn (signatureComplexity . view _2) (toList sigsWhichOccurred)) where  
    numsToSimulateAt :: NonEmpty Natural
    numsToSimulateAt = 4 :| [5.. 5]
    pairsToSimulateAt :: NonEmpty (Int, Natural)
    pairsToSimulateAt = (\x -> (fromIntegral $ 1200, x)) <$> numsToSimulateAt
    -- the simulation history and the displacement history
    simsAtNums :: NonEmpty ([(Phase, ExpTape Bit Count)], [Int])
    simsAtNums = let 
      ans = (\(x,y) -> simForStepNumFromConfig x machine
        $ replaceSymbolVarInConfig config varToGeneralize
        $ FinCount y) <$> pairsToSimulateAt
      msg = toString $ T.intercalate "startsim:\n" $ (\x -> "length: " <> show (length x) <> "\n" <> displayHist x) . 
        fmap (fmap (second NotInfinity)) . fst <$> toList ans
      in
      trace msg ans
    --occurred in all simulations 
    sigsWhichOccurred :: Set (Phase, Signature Bit)
    sigsWhichOccurred = let
        (sig1 :| restSignatures) = fromList . fmap (fmap tapeSignature) . view _1 <$> simsAtNums
        ans = foldr S.intersection sig1 restSignatures
        msg = toString $ T.intercalate "\n" $ show <$> toList ans
      in trace msg ans
    --generalizes an ending signature if possible
    generalizeOneSig :: (Phase, Signature Bit) -> Maybe (Skip Count Bit)
    generalizeOneSig psb@(_p, sigToGeneralize) = trace ("generalizing\n" <> show sigToGeneralize)
      res where
        munge :: [(Phase, ExpTape Bit Count)] -> (Int, (Phase, ExpTape Bit Count))
        munge hist = case findIndex (\(p, t) -> (p, tapeSignature t) == psb) hist of
            Nothing -> error "there was nothing with a signature we checked is in everything"
            Just i -> (i, hist !! i)
        --for each hisory, the time at which the signature occured, and the simstate at that point
        finalIndexAndConfig :: [(Int, (Phase, ExpTape Bit Count))]
        finalIndexAndConfig = let
             ans = munge . view _1 <$> toList simsAtNums
             msg = "final indices and configs\n" <> toString (T.intercalate "\n" $ show . pretty <$> ans)
            in 
                trace msg ans 
        finalIndices = view _1 <$> finalIndexAndConfig
        finalPhases = view (_2 . _1) <$> finalIndexAndConfig
        finalPhase :: Maybe Phase
        finalPhase = guard (allEqual finalPhases) $> U.head finalPhases
        slicedPairs :: [(ExpTape Bit Count, ExpTape Bit Count)]
        slicedPairs = getZipList $ liftA2
            (\i (hist, disps) -> getSlicePairC hist disps 0 i)
            (ZipList finalIndices)
            (ZipList $ toList simsAtNums)
        countLists :: [(([Count], [Count]), ([Count], [Count]))]
        countLists = fmap (bimapBoth getCounts) slicedPairs
        --genrealizes against the numsToSimulateAt from above 
        generalizeCL :: [Count] -> Maybe Count
        generalizeCL cl = snd <$> (generalizeFromCounts =<< nonEmpty (zipExact (FinCount <$> toList numsToSimulateAt) cl))
        getAtF f = traverse generalizeCL $ transpose (f <$> countLists)
        --we want to push the outer list all the way to the inside 
        transposedCountLists :: Maybe (([Count], [Count]), ([Count], [Count]))
        transposedCountLists = (\x y z w -> ((x, y),(z,w))) <$> getAtF (fst . fst) <*> getAtF (snd . fst) <*> getAtF (fst.snd) <*> getAtF (snd.snd)
        res = do
            ((_s_cls, _s_crs), (e_cls, e_crs)) <- transposedCountLists
            e_ph <- finalPhase
            let end_points = point . view (_2 . _2) <$> finalIndexAndConfig
            guard $ allEqual end_points
            pure $ Skip
                (replaceSymbolVarInConfig config varToGeneralize (boundVarCount (BoundVar 0) 1))
                -- we have the e_cls and the e_crs, and we have psb which is the final phase 
                --and signature we're trying to generalize across, so we just need to write 
                -- Signature Bit -> ([Count], [Count]) -> ExpTape Bit Count with zipExact
                (EndMiddle $ etToConfig e_ph $ zipSigToET sigToGeneralize (e_cls, e_crs))
                (FinCount 100) False Zero --TODO

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

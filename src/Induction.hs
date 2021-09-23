module Induction where

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)
import qualified Data.Map as M

import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
import Data.Bits (Bits(bit))
import Data.List (minimumBy)
import Relude.Extra (bimapBoth)
import Relude.Foldable (Bitraversable)
import Safe.Exact

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
replaceVarInSkip (Skip sConfig eSE hopCount halts) varIn countOut =
    Skip newConfig newSE (replaceVarInCount hopCount) halts where
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
proveBySimulating limit t book (Skip start goal _ _)
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
            MachineStuck -> Left $ "machine stuck " <> show p
                <> " " <> show goal <> " " <> show tape
            Stepped Infinity _ _ _ -> Left "hopped to infinity"
            Stepped (NotInfinity hopsTaken) newPhase newTape _
                -> loop (numSteps + 1) newPhase newTape (curCount <> hopsTaken)
    indMatch :: Phase -> ExpTape Bit InfCount -> SkipEnd Bit -> Bool
    indMatch cur_p et se = case bitraverse pure deInfCount et of
        Nothing -> False
        Just tape@(ExpTape ls point rs) -> case se of
            EndMiddle (Config ph c_ls c_p c_rs)
                -> (cur_p == ph) && (ls == c_ls) && (point == c_p) && (rs == c_rs)
            EndSide goalPhase dir xs -> endSideTapeMatch dir xs tape &&
                endSideTransMatch dir goalPhase t cur_p tape
      where
        endSideTapeMatch :: Dir -> [(Bit, Count)] -> ExpTape Bit Count -> Bool
        endSideTapeMatch L goal (ExpTape _ls point rs) = case getNewFinPoint goal of
            Nothing -> False
            Just (goal_p, goal_xs) -> (goal_p == point) && (goal_xs == rs) --yes this is reversed
        endSideTapeMatch R goal (ExpTape ls point _rs) = case getNewFinPoint goal of
            Nothing -> False
            Just (goal_p, goal_xs) -> (goal_p == point) && (goal_xs == ls) --yes this is reversed
        endSideTransMatch :: Dir -> Phase -> Turing -> Phase ->  ExpTape Bit Count -> Bool
        endSideTransMatch goal_d goalPhase (Turing _n map) curPhase (ExpTape _ p _)
            = case map ^. at (curPhase, p) of
                Nothing -> False
                (Just Halt) -> goal_d == L
                (Just (Step transPhase _bit d)) -> goal_d == d && goalPhase == transPhase
        deInfCount Infinity = Nothing
        deInfCount (NotInfinity c) = Just c

transposeNE :: NonEmpty [a] -> [NonEmpty a]
transposeNE (x :| xs) = (:|) <$> x <*> transpose xs

bitraverseBoth :: (Bitraversable p, Applicative f) => (a -> f b) -> p a a -> f (p b b)
bitraverseBoth f = bitraverse f f

list1AllEqual :: (Ord a) => NonEmpty a -> Bool
list1AllEqual (x :| rest) = all (== x) rest

boolToMaybe :: Bool -> Maybe ()
boolToMaybe True = Just ()
boolToMaybe False = Nothing

-- TODO: write a function that guesses a good induction hypothesis given a history of the tape 
-- (first guess: the simplest signature that has occurred 3 times, guess the additive induction if one exists)
guessInductionHypothesis :: [ExpTape Bit InfCount] -> Maybe (Skip Bit)
guessInductionHypothesis tapes = skipOut where
    tapeSignatures :: [Signature Bit]
    tapeSignatures = tapeSignature <$> tapes
    sigFreqs :: Map (Signature Bit) Int
    sigFreqs = M.fromListWith (+) $ (,1) <$> tapeSignatures
    possibleSigs :: [Signature Bit]
    possibleSigs = filter (\s -> (sigFreqs ^?! ix s) >= 3) tapeSignatures
    simplestSig = minimumBy (compare `on` signatureComplexity) possibleSigs
    goalTapes :: Maybe (NonEmpty (ExpTape Bit InfCount))
    goalTapes = nonEmpty $ filter (\tape -> tapeSignature tape == simplestSig) tapes
    --To complete this function, given the goal tapes, for each position, accumulate the counts at that position
    --a list of counts leads to a generalized guess for the overall (more complex) count, eg 1, 2, 3, leads to n, and 2,4,6 leads to 2n
    -- then you need to be able to union counts somehow maybe? or no, I think that's just it
    etToCounts (ExpTape ls _p rs) = (snd <$> ls, snd <$> rs)
    countOfGoalTapes :: Maybe (NonEmpty ([InfCount], [InfCount]))
    countOfGoalTapes = etToCounts <$$> goalTapes
    pairOfCountLists :: Maybe ([NonEmpty InfCount], [NonEmpty InfCount])
    pairOfCountLists = bisequence (transposeNE <$> (fst <$$> countOfGoalTapes),
                                   transposeNE <$> (snd <$$> countOfGoalTapes))
    pairUpNe :: NonEmpty a -> [(a, a)]
    pairUpNe xs = (,) <$> init xs <*> tail xs
    pairOfCountPairs :: Maybe ([NonEmpty (InfCount, InfCount)], [NonEmpty (InfCount, InfCount)])
    pairOfCountPairs =  bimapBoth (fmap $ fromList . pairUpNe) <$> pairOfCountLists
    allCountsGeneralizedEither :: Maybe ([Either () (Count, Count)], [Either () (Count, Count)])
    allCountsGeneralizedEither = bitraverseBoth (traverse generalizeFromInfCounts) =<< pairOfCountPairs
    mungeGeneralizedCount :: [Either () (Count, Count)] -> [(Count, Count)] 
    mungeGeneralizedCount = \case 
        [] -> [] 
        [x] -> case x of 
            Left () -> [] 
            Right p -> [p] 
        x : rest@(_: _) -> case x of 
            Left () -> error "mungeGeneralizedCount"
            Right p -> p : mungeGeneralizedCount rest 
    allCountsGeneralized = bimapBoth mungeGeneralizedCount <$> allCountsGeneralizedEither
    goalPoints :: Maybe (NonEmpty Bit)
    goalPoints = point <$$> goalTapes
    targetPoint :: Maybe Bit
    targetPoint = head <$> goalPoints
    etPointsStacked :: Maybe Bit --really worried I got this one wrong -- 23:50 29Sep21
    etPointsStacked = (boolToMaybe . list1AllEqual =<< goalPoints) >> targetPoint
    skipOut = do 
        (lPairs, rPairs) <- allCountsGeneralized 
        point <- etPointsStacked 
        (Signature lSig p rSig) <- tapeSignature . head <$> goalTapes 
        if p /= point then error "oh no skipOut" else Just () 
        let 
         makeConfig f = Config undefined (zipExact lSig (f <$> lPairs)) p (zipExact rSig (f <$> rPairs)) 
         startConfig = makeConfig fst 
         endConfig = makeConfig snd 
        pure $ Skip startConfig (EndMiddle endConfig) (finiteCount 0) False

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
    naturalPairs = traverse (bitraverse countToMaybeNat countToMaybeNat) xs
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
    conformsToAffine m b (x, y) = (fromIntegral x * fromIntegral m + b) == fromIntegral y
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
                    then (y2 - y1) `maybeDiv` (x2 - x1)
                    else (y1 - y2) `maybeDiv` (x1 - x2)
            let b :: Int = fromIntegral y1 - (fromIntegral m * fromIntegral x1)
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

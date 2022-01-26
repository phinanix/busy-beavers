module Induction where

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs, keysSet)
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import Prettyprinter
import Data.Either.Combinators

import Data.Bits (Bits(bit))
import Data.List (minimumBy, findIndex)
import qualified Data.List.NonEmpty as NE
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
import HaltProof
import Glue
import Data.Bifoldable (Bifoldable)
import Graphs
import Data.Bitraversable

{-
27 Nov 21 
Shortrange plan to get a thing which can prove the counter machine into main
- make a filter for "interesting skip" since rn "whathappensnext" proves a bunch of useless stuff 
   (means a skip has a var probably)
- write proveInductivelyIMeanIt which does 
  - guessInductionHypothesis
  - attempts proveInductively on same
  - if that gets stuck (modify ^ to return stuckness), then attempts guessWhatHappensNext
  - if any of those return as interesting, re-attempt to proveInductively the original hypothesis
  - (bonus) if stuck again, return to above if stuck on a new thing, up to a finite limit
  - one round of this should be enough to prove the counter!
  - write / integrate the thing which checks whether a skip allows you to prove the machine runs forever, and if so,
    then you return a haltproof
- also fix all the tests >> 
- and do the bwsearch DFS thing whenever
-}

--we need the current step for the haltproof
--we always return the new book
--we return either a haltproof, or a text saying how we failed
proveInductivelyIMeanIT :: Turing -> SkipBook Bit -> Steps -> TapeHist Bit InfCount -> DispHist
    -> (SkipBook Bit, Either Text (Skip Count Bit))
proveInductivelyIMeanIT machine book curStep hist dispHist
  = --force $ 
  case guessInductionHypothesis hist dispHist of
    Left msg -> (book, Left $ "failed to guessIndHyp:\n" <> msg)
    Right indHyp -> let (newBook, tOrOrigin) = proveStrong 5 machine book indHyp (BoundVar 0) in
      case tOrOrigin of
        Left msg -> (newBook, Left $ "couldn't prove indHyp, which was:\n" <> showP indHyp <> "\nbecause:\n" <> msg)
        Right origin -> let finalBook = addSkipToBook indHyp origin newBook
         in (finalBook, Right indHyp)


--the function that does most of the work alternates two functions:
--proveOrStuck, which is a slight modification of proveInductively to tell you where it is stuck, and
--guessAndProveWhatHappensNext, which the program uses to try to get unstuck
--the latter makes no progress if it proves 0 things, which is one way to abort
--the former makes no progress if it gets stuck on the same thing as last time, which we note in order to track
--we also as usual put a finite integer on the number of loops we can do, although hitting that would be pretty insane
proveStrong :: Int -> Turing -> SkipBook Bit -> Skip Count Bit -> BoundVar -> (SkipBook Bit, Either Text (SkipOrigin Bit))
proveStrong loopLim machine book goal indVar = swapEither <$> loop 0 book Nothing where
  -- the skiporigin is one for specifically the goal 
  -- the text is "we failed"
  loop :: Int -> SkipBook Bit -> Maybe (Config Count Bit) -> (SkipBook Bit, Either (SkipOrigin Bit) Text)
  loop idx curBook mbLastStuck = --trace ("provestrong loop " <> show idx <> "\n") $
    if idx > loopLim then error "wow we exceeded looplim!" -- Right "limit exceeded" 
    else case proveInductively 100 machine curBook goal indVar of
      Right skipOrigin -> (curBook, Left skipOrigin)
      Left (msg, maybeStuckConfig) -> --trace ("stuck on:\n" <> show (pretty maybeStuckConfig) <> "\nbecause:\n" <> toString msg) $
        if has _Just mbLastStuck && mbLastStuck == maybeStuckConfig
          then (curBook, Right $ "got stuck on same thing twice:\n" <> show (pretty mbLastStuck))
        else if (thingContainsVar <$> maybeStuckConfig) == Just False
          then (curBook, Right $ "got stuck on something with no vars:\n" <> show (pretty maybeStuckConfig))
        else case maybeStuckConfig of
          Nothing -> (curBook, Right $ "proveInd failed not due to being stuck:\n" <> msg)
          Just stuckConfig -> let scatter = guessAndProveWhatHappensNext machine curBook stuckConfig (SymbolVar 0) in
            if null scatter
              then (curBook, Right $ "guessAndProveWhatHappensNext did not get us unstuck from:\n" <> show (pretty stuckConfig))
              else let newBook = addMultipleToBook scatter curBook in
                loop (idx + 1) newBook (Just stuckConfig)


isSameInAsOut :: forall c s. (Monoid c, Eq c) => Skip c s -> Bool 
isSameInAsOut (Skip start end _ _ _) = addUp start == addUp end
  where 
    addUp :: (Bifoldable b) => b c s -> c 
    addUp = bifoldMap id (const mempty)
  
--goal: make a thing that takes a skip that might apply to a certain machine, 
--attempts to simulate forward to prove that skip using induction
-- the first int is the limit on the number of steps to take before giving up 
--the (skip bit) input is the goal to be proven, 
-- the BoundVar is the variable on which we are going to do induction
--returns Left with an error message, and the config we got stuck on 
--or Right with success
proveInductively :: Int -> Turing -> SkipBook Bit -> Skip Count Bit -> BoundVar
    -> Either (Text, Maybe (Config Count Bit)) (SkipOrigin Bit)
proveInductively limit t book goal indVar = let 
  ans =  -- <> "using book\n" <> show (pretty book)) $
    --force $
    case baseCase of
      Left res -> Left $ first ("failed base: " <>) res
      Right _ -> case indCase of
        Left res -> Left $ first ("failed ind: " <>) res
        Right _ ->  pure origin
  msg = ("trying to prove:\n" <> show (pretty goal)) <> "\ngot res" <> show ans
    in --force $
      -- trace msg $
      assert (isSameInAsOut goal) ans 
    where
    origin :: SkipOrigin Bit
    origin = Induction book limit
    baseCase :: Either (Text, Maybe (Config Count Bit)) Count
    baseCase = proveSimLinearAndTree limit limit t book baseGoal
    baseGoal :: Skip Count Bit
    baseGoal = replaceVarInSkip goal indVar $ finiteCount 1 --TODO, should be 1
    setStepCount steps skip = skip & hops .~ FinCount steps
    goalPlusX x = --setStepCount 100 $ 
      replaceVarInSkip goal indVar $ FinCount x <> symbolVarCount newSymbolVar 1
    indCase :: Either (Text, Maybe (Config Count Bit)) Count
    --this doesn't actually add the inductive hypothesis to the book!
    indCase = --trace "\nstarting ind\n" $ 
      --deepseq indHyp $
        proveSimLinearAndTree limit limit t
         (addSkipToBook indHyp InductionHypothesis book)
         indGoal
    indHyp :: Skip Count Bit
    indHyp = let
        --TODO: make the hypothesis be 0 and the goal be 1 again
        ans = goalPlusX 0
        msg = "indHyp is:\n" <> show (pretty ans)
      in
        --force 
        -- $ trace msg
        ans
    indGoal :: Skip Count Bit
    indGoal = goalPlusX 1
    newSymbolVar :: SymbolVar --TODO: this is obviously incredibly unsafe
    newSymbolVar = SymbolVar 0

--first int is linear step limit, second int is tree step limit
proveSimLinearAndTree :: Int -> Int -> Turing -> SkipBook Bit -> Skip Count Bit -> Either (Text, Maybe (Config Count Bit)) Count
-- simulateViaDFS :: Int -> Int -> SkipBook Bit -> Skip Count Bit -> Either Text Natural 
proveSimLinearAndTree linStep treeStep machine book skip 
  = --force $ 
  case simulateViaDFS linStep treeStep book skip of 
    --TODO: this blurs the line of what the returned count means, between big steps and small steps
    Right nat -> Right $ FinCount nat 
    Left text -> case proveBySimulating linStep machine book skip of 
      --works if you comment out this error and return right, but HOW COULD THAT BE TRUE you should never hit this error
      --the reason for this is simulateViaDFS should guess the same as proveBySimulating as it's first deep path, and should only recurse onto 
      --other paths if that doesn't work
      --but if proveBySimulating returns success, it seems to work, which is a contradiction
      --oh dear, maybe part of the issue is whether "simulateViaDFS" and "proveBySimulating" are using "big steps" or "little steps"? 
      --because the error occurs with count=467 which seems to be bigger than the callsite (guessAndProveWhatHappensNext), 
      --which calls with a limit of 200 afaict 
      Right count -> error $ "what? count: " <> showP count <> " linstep:" <> showP linStep <> " treestep: " <> showP treeStep 
                            <> "\nmachine was\n" <> showP machine <> "\nwe were proving:\n" <> showP skip
                            <> "\ndfs failed because:" <> text 
                            <> "\nbook was:\n" <> showP book 
      res@(Left _) -> res 

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
    replaceVarInCount = replaceBoundVarInCount varIn countOut 

replaceBoundVarInCount :: BoundVar -> Count -> Count -> Count
replaceBoundVarInCount varIn countOut (Count num symbolMap boundMap) =
    Count num symbolMap Empty <> foldMap updateVar (assocs boundMap) where
        updateVar (v, Sum n) = if v == varIn
            then n `nTimes` countOut
            else boundVarCount v n

-- input int is limit on number of steps to simulate
-- output count is the number of steps it actually took 
-- the text tells you why you failed, and you might have failed via getting "stuck" on something, in which case we return that
-- this linearly simulates forward, which sometimes gets you into a hole when you prove something that skips ahead, because 
-- you can end up skipping past the thing you want. to solve this problem, I wrote simulateviadfs
proveBySimulating :: Int -> Turing -> SkipBook Bit -> Skip Count Bit -> Either (Text, Maybe (Config Count Bit)) Count
proveBySimulating limit t book (Skip start goal _ _ _) = let 
  ans = loop 0 (start ^. cstate) (second NotInfinity $ configToET start ^. _2) (finiteCount 0)
  msg = "starting pos:\n" <> show (pretty start) <> "\nsucceeded: " <> show (has _Right ans)
      <> "\nans:" <> showP ans 
  in
    --force $ 
    --trace msg 
    ans 
    where
    -- four conditions: we've taken more steps than the limit,
    -- we've succeeded, stepping fails for some reason, or we continue 
    loop :: Int -> Phase -> ExpTape Bit InfCount -> Count -> Either (Text, Maybe (Config Count Bit)) Count
    loop numSteps p tape curCount
      -- | trace (Unsafe.init $ toString $ "steps:" <> show numSteps <> " count:" <> showP curCount <>
      --            " p:" <> dispPhase p <> " tape is: " <> dispExpTape tape) False = undefined
      | indMatch p tape goal = pure curCount
      | numSteps > limit = Left ("exceeded limit while simulating", Nothing)
      | otherwise = case skipStep t book p tape of
            Unknown e -> Left ("hit unknown edge" <> show e, Nothing)
            Stopped {} -> Left ("halted while simulating", Nothing)
            MachineStuck -> let
                stuckConfig = etToConfig p $ second deInfCount tape
                msg = "machine stuck on step: " <> show numSteps
                  <> " in phase:" <> show p
                  <> "\ngoal:" <> show (pretty goal) <> "\ncur tape:" <> dispExpTape tape
                in
                Left (msg, Just stuckConfig)
            Stepped Infinity _ _ _ _ _ -> Left ("hopped to infinity", Nothing)
            Stepped (NotInfinity hopsTaken) newPhase newTape _ _ _
                -> loop (numSteps + 1) newPhase newTape (curCount <> hopsTaken)
    indMatch :: Phase -> ExpTape Bit InfCount -> SkipEnd Count Bit -> Bool
    indMatch cur_p et se = case bitraverse pure mbdeInfCount et of
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
        mbdeInfCount Infinity = Nothing
        mbdeInfCount (NotInfinity c) = Just c

--TODO, it's really dumb we have to "deInfCount here"
getNextConfigs :: SkipBook Bit -> Config Count Bit -> [Config Count Bit]
getNextConfigs book curConfig = first deInfCount . view (_2 . resConfig) <$> choices
 where
  choices :: [(Skip Count Bit, SkipResult Bit InfCount)]
  --flip since sort gives smallest to largest by default but we want the largest skip first
  choices = sortBy (flip skipFarthest) $ uncurry (getSkipsWhichApply book) (configToET $ first NotInfinity curConfig)

--the text is why you failed, and the count is how many big steps 
simulateViaDFS :: Int -> Int -> SkipBook Bit -> Skip Count Bit -> Either Text Natural 
simulateViaDFS stepLim depthLim book (Skip startConfig skipEnd _hops _halts _disp) = case res of 
  Right (Success vs) -> Right $ fromIntegral $ length vs
  --the problem here is we sort of want some kind of like 'what did the DFS get stuck on' list 
  --but that's not something we have right now
  Right NoSuccess -> Left "dfs exhaustively searched with no results"
  Left message -> Left $ "failed dfs: " <> message
  where 
    res = case preview _EndMiddle skipEnd of 
      Nothing -> Left "target skip did not endmiddle"
      Just endConfig -> dfs stepLim depthLim (getNextConfigs book) (== endConfig) startConfig 
    
transposeNE :: NonEmpty [a] -> [NonEmpty a]
transposeNE (x :| xs) = getZipList $ (:|) <$> ZipList x <*> ZipList (transpose xs)

transposeOverPair :: forall a. NonEmpty ([a], [a]) -> ([NonEmpty a], [NonEmpty a])
transposeOverPair xs = bimapBoth transposeNE $ NE.unzip xs

transposeOverTwoPairs :: NonEmpty (([a], [a]), ([a], [a])) -> (([NonEmpty a], [NonEmpty a]), ([NonEmpty a], [NonEmpty a]))
transposeOverTwoPairs xs = bimapBoth (bimapBoth transposeNE) $ bimapBoth NE.unzip $ NE.unzip xs

test :: NonEmpty [a] -> [NonEmpty a]
test = sequenceA 

bifoldMapBoth :: (Bifoldable p, Monoid m) => (a -> m) -> p a a -> m 
bifoldMapBoth f = bifoldMap f f

bitraverseBoth :: (Bitraversable p, Applicative f) => (a -> f b) -> p a a -> f (p b b)
bitraverseBoth f = bitraverse f f

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

possibleSignatures :: [(Phase, ExpTape Bit InfCount)] -> [(Phase, Signature Bit)]
possibleSignatures hist = filter (\s -> --let msg = ("ixing: " <> showP s <> "\n in map:\n" <> show (sigFreqs)) in trace msg $
  sigFreqs ^?! ix s >= 3) tapeSignatures where
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
guessCriticalConfiguration :: [(Phase, ExpTape Bit InfCount)] -> Either Text (Phase, Signature Bit)
guessCriticalConfiguration hist = case possibleSignatures hist of 
  [] -> Left "no possible criticalconfigs"
  xs -> Right $ minimumBy (compare `on` signatureComplexity . snd) xs

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
calcCommonSig start end = -- trace ("commonsig-ing " <> show start <> " and " <> show end) $
  asum $ check <$> tf <*> tf where
    tf = [False, True]
    check dl dr = do 
      let
        lFunc = if dl then dropLeft else pure 
        rFunc = if dr then dropRight else pure 
      dropped_start <- lFunc =<< rFunc start
      if dropped_start == end then Just (dl, dr) else Nothing
    dropLeft (Signature ls p rs) = do 
      ls' <- viaNonEmpty init ls 
      pure $ Signature ls' p rs
    dropRight (Signature ls p rs) = do 
      rs' <- viaNonEmpty init rs 
      pure $ Signature ls p rs' 

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

guessInductionHypothesis :: TapeHist Bit InfCount -> DispHist -> Either Text (Skip Count Bit)
guessInductionHypothesis (TapeHist hist) (DispHist disps) = 
  do
  criticalConfig@(criticalPhase, _criticalSignature) <- guessCriticalConfiguration hist
  let
    configIndicesAndConfigs = obtainConfigIndices hist criticalConfig
    configIndices = let ans = fst <$> configIndicesAndConfigs in 
      --trace ("configIndices were: " <> showP ans) 
      ans
    indexPairs = zipExact (U.init configIndices) (U.tail configIndices)
    slicePairs = uncurry (getSlicePair hist disps) <$> indexPairs
    allSigs = let ans = fmap (bimapBoth tapeSignature) slicePairs in 
      --trace ("allsigs were: " <> showP ans) 
      ans
  --only proceed from here if all the pairs have the same signature at both the start and the end
  if allEqual allSigs then Right () else Left "sigs were not all equal"
  --to finish from here, our goal is for each transition start -> end, make a bunch of pairs of counts 
  --and then to generalize those pairs of counts accross all the transitions
  --to do this, we have to find a "common signature" for the start and end - we have allowed them to be 
  --different for the moment
  (startSig, endSig) <- failMsg "no sigs" $ viaNonEmpty head allSigs
  toDrop <- failMsg "failed common sig" $ calcCommonSig startSig endSig
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
  thingsToGeneralizeList <- failMsg "list was empty" $ 
    bitraverseBoth (traverse nonEmpty) $ transposePairs countPairListList
  --the pair here is over left and right, then the list is over the "signature dimension", and the internal
  --pair is over start -> finish
  allThingsGeneralized <- failMsg "failed to generalize"  $ 
    bitraverseBoth (traverse generalizeFromCounts) thingsToGeneralizeList
  --we want to pull the pair from start -> finish out to the front, then have the left right pair, then have the 
  --"signature dimension"
  let startCounts = bimapBoth (fmap fst) allThingsGeneralized
      endCounts =  bimapBoth (fmap snd) allThingsGeneralized
      startConfig = combineIntoConfig criticalPhase startCounts startSig
      endConfig = combineIntoConfig criticalPhase endCounts endSig
      ans = Skip startConfig (EndMiddle endConfig) Empty False Zero
      msg = "guessed " <> showP ans
  --force $
    -- $ trace msg 
  assert (isSameInAsOut ans) $ pure ans
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

zipSigToET :: (Partial, Show b, Pretty c) => Signature b -> ([c], [c]) -> ExpTape b c
zipSigToET sig@(Signature b_ls p b_rs) pair@(c_ls, c_rs) = let
    ans = ExpTape (zipExact b_ls c_ls) p (zipExact b_rs c_rs)
    in
    -- trace ("zipping:\n" <> show (show sig <> "\n" <> pretty pair) <> "\nzipped\n") 
    ans

--gets the simulation history and the displacement history
--normally these are output backwards which is of course crazy so we fix them here 
simForStepNumFromConfig :: Partial => Int -> Turing -> Config Count Bit -> (TapeHist Bit Count, DispHist)
simForStepNumFromConfig limit machine startConfig
    = (second deInfCount $ finalState ^. s_history, finalState ^. s_disp_history)
    where
    (startPh, startTape) = second (second NotInfinity) $ configToET startConfig
    actionList = simulateStepUntilUnknown limit :| [liftModifyState recordHist, liftModifyState recordDispHist]
    res = simulateOneMachineOuterLoop actionList machine (skipStateFromPhTape machine startPh startTape)
    finalState = last $ snd res

replaceSymbolVarInConfig :: Partial => Bool -> Config Count s -> SymbolVar -> Count -> Config Count s
replaceSymbolVarInConfig runAssert config sv ans
    = (if runAssert then assert (configContainsSymbolVar sv config) else id)
      first replaceSymbolVarInCount config where
        replaceSymbolVarInCount :: Count -> Count
        replaceSymbolVarInCount (Count n as xs) = Count n Empty xs <> foldMap updateVar (assocs as) where
            updateVar (v, Sum n) = if v == sv then n `nTimes` ans else symbolVarCount v n
        configContainsSymbolVar sv = getAny . bifoldMap (Any . countContainsSymbolVar sv) (const mempty)
        countContainsSymbolVar :: SymbolVar -> Count -> Bool
        countContainsSymbolVar sv = \case
          (Count _n as _xs) -> has (ix sv) as

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
guessWhatHappensNext :: Turing -> Config Count Bit -> SymbolVar -> [Skip Count Bit]
guessWhatHappensNext machine startConfig varToGeneralize
 = mapMaybe generalizeOneSig (--force $ 
 toList sigsWhichOccurred) where
    -- minimumComplexity = minimum $ signatureComplexity . view _2 <$> toList sigsWhichOccurred
    -- sigsOfMinComplexity = filter (\x -> signatureComplexity (view _2 x) == minimumComplexity) $ toList sigsWhichOccurred
    numsToSimulateAt :: NonEmpty Natural
    numsToSimulateAt = 3 :| [4.. 7]
    pairsToSimulateAt :: NonEmpty (Int, Natural)
    pairsToSimulateAt = (\x -> (2000, x)) <$> numsToSimulateAt
    -- the simulation history and the displacement history
    simsAtNums :: NonEmpty ([(Phase, ExpTape Bit Count)], [Int])
    simsAtNums = let
      ans = bimap getTapeHist getDispHist <$> ((\(x,y) -> simForStepNumFromConfig x machine
        $ replaceSymbolVarInConfig True startConfig varToGeneralize
        $ FinCount y) <$> pairsToSimulateAt)
      msg = toString $ T.intercalate "startsim:\n" $ (\x -> "length: " <> show (length x) <> "\n" <> displayHist x) .
        fmap (fmap (second NotInfinity)) . fst <$> toList ans
      in
      --trace msg 
      ans
    --occurred in all simulations 
    sigsWhichOccurred :: Set (Phase, Signature Bit)
    sigsWhichOccurred = let
        (sig1 :| restSignatures) = fromList . fmap (fmap tapeSignature) . view _1 <$> simsAtNums
        ans = foldr S.intersection sig1 restSignatures
        msg = "allSigs occurred were:" <> toString (T.intercalate "\n" $ show <$> toList ans) <> "end allsigsoccured\n"
      in --force 
        -- $ trace msg 
        ans
    --generalizes an ending signature if possible
    generalizeOneSig :: (Phase, Signature Bit) -> Maybe (Skip Count Bit)
    generalizeOneSig psb@(_p, sigToGeneralize) = --force $ --trace ("generalizing\n" <> show sigToGeneralize)
      res where
        munge :: [(Phase, ExpTape Bit Count)] -> (Int, (Phase, ExpTape Bit Count))
        munge hist = case findIndex (\(p, t) -> (p, tapeSignature t) == psb) hist of
            Nothing -> error "there was nothing with a signature we checked is in everything"
            Just i -> (i, hist !! i)
        --for each hisory, the time at which the signature occured, and the simstate at that point
        finalIndexAndConfig :: NonEmpty (Int, (Phase, ExpTape Bit Count))
        finalIndexAndConfig = let
             ans = munge . view _1 <$>  simsAtNums
             msg = "final indices and configs\n" <> toString (T.intercalate "\n" $ toList $ show . pretty <$> ans)
            in
          -- trace msg 
                ans
        finalIndices = view _1 <$> finalIndexAndConfig
        finalPhases = view (_2 . _1) <$> finalIndexAndConfig
        finalPhase :: Maybe Phase
        finalPhase = guard (list1AllEqual finalPhases) $> head finalPhases
        --the problem is these slicedpairs may not all have the same signature as the original thing 
        --which we are trying to generalize
        --generalizes against the numsToSimulateAt from above 
        --the outer maybe is in case we fail. the inner maybe is because sometimes we don't generalize against the simnum at all, 
        --in which case the simnum is irrelevant 
        generalizeCL :: Partial => NonEmpty Count -> Maybe (Maybe Count, Count)
        generalizeCL cl = if list1AllEqual cl
            then Just (Nothing, head cl)
            --the problem with discarding the fst element of this pair, is that if you generalize (3,1) (4,2), then the first
            --the pair is (x + 2, x), but by discarding the first element, you're implcitly assuming it's x, more-or-less, so 
            --that ends up not working 
            else let 
              f = (FinCount <$> numsToSimulateAt) 
              s = cl
              m1 = "zipping:" <> showP f <> " " <> showP s
              ans = 
                --trace m1 $ 
                first pure <$> generalizeFromCounts (neZipExact f s)
              msg = "generalized:" <> show (pretty cl) <> "\ngot\n" <> show (pretty ans)
            in 
              -- trace msg 
              ans 
        {-algorithm:
        first, generalize all the counts to pairs, with the simnum we put in. you might think we're done now, and we just want the 
        second number of this pair. I also thought this, but that is not correct, because in the two pairs (x, x) (x + 2, x), that
        second x does not mean the same thing!
        therefore, the second thing to do is to make a big list of all the first elements of the pairs, and calculate their 
        "maximum" (smallest thing you can add something to all of them to get). 
        Third, map across all the pairs again, adding to both elements whatever it takes to get the first element to the maximum, and 
        then discarding the first element, to leave just the second element. 
        -}
        bigTraverse = bitraverseBoth . bitraverseBoth . traverse 
        --bigMap = bimapBoth . bimapBoth . fmap
        --transposedCountLists = bitraverseBoth (bitraverseBoth (traverse generalizeCL)) flippedCountLists
        res = do
            let slicedPairs :: NonEmpty (ExpTape Bit Count, ExpTape Bit Count)
                slicedPairs = let
                  ans = (\(i, (hist, disps)) -> getSlicePairC hist disps 0 i) <$>
                    neZipExact finalIndices simsAtNums
                  msg = "slicedPairs were:\n" <> show (pretty ans)
                  in
                  --trace msg 
                    ans
                countLists :: NonEmpty (([Count], [Count]), ([Count], [Count]))
                countLists = fmap (bimapBoth getCounts) slicedPairs
                flippedCountLists = transposeOverTwoPairs countLists 
            --after you slice them, they may no longer all be the same signature
            --for now, lets just assume they are
            guard $ list1AllEqual $ fmap (bimapBoth tapeSignature) slicedPairs
            countPairLists <- --trace ("flipcountls" <> showP flippedCountLists) 
              bigTraverse generalizeCL flippedCountLists
            let listOfFirstElements = (bifoldMapBoth . bifoldMapBoth . foldMap) (maybeToList . fst) countPairLists 
                --todo does this do the right thing
                maxFirstElt = case listOfFirstElements of 
                  [] -> error "empty list of first elements"
                  (x : xs) -> maximum listOfFirstElements 
            ((s_cls, s_crs), (e_cls, e_crs)) <- bigTraverse (resolveCountPair maxFirstElt) countPairLists 
            --todo, we probably shouldn't get the start counts from the aggregator, because that is kind of bad, compared to 
            --getting them from the startConfig. the problem is, we also need to slice the startConfig somehow, and that's 
            --actually quite hard. 
            --actually not sure this is right on more consideration            
            e_ph :: Phase <- finalPhase
            let end_points = point . view (_2 . _2) <$> finalIndexAndConfig
            guard $ list1AllEqual end_points
            let startSignatures = tapeSignature . fst <$> slicedPairs
                endSignatures = tapeSignature . snd <$> slicedPairs
            guard $ list1AllEqual startSignatures && list1AllEqual endSignatures
            let startSig = head startSignatures
                endSig = head endSignatures
                guessedStartConfig = etToConfig (startConfig ^. cstate) $ zipSigToET startSig (s_cls, s_crs)
                skipOut = Skip
                  (replaceSymbolVarInConfig False guessedStartConfig varToGeneralize (boundVarCount (BoundVar 0) 1))
                  -- we have the e_cls and the e_crs, and we have psb which is the final phase 
                  --and signature we're trying to generalize across, so we just need to write 
                  -- Signature Bit -> ([Count], [Count]) -> ExpTape Bit Count with zipExact
                  (EndMiddle $ etToConfig e_ph $ zipSigToET endSig (e_cls, e_crs))
                  (FinCount 100) False Zero --TODO
                msg = "guessedWhatsNext " <> showP skipOut 
            assert (endSig `isSubSignatureOf` sigToGeneralize) $
              --force $ trace msg $ 
              assert (isSameInAsOut skipOut) $
              pure skipOut 

{- We're trying to get the first element of the pair to be target, which will require modifying 
the second element, which we then return. if the first element is Nothing, it can be whatever and
thus we can just return the second element. 
To make the first element be equal to the target, we're going to try to substitute one variable 
in the first element to be equal to some of the second variable 
-}
resolveCountPair :: Count -> (Maybe Count, Count) -> Maybe Count 
resolveCountPair target = \case
  (Nothing, s) -> Just s
  (Just f@(OneVar n as k x), s) -> do
    let (Count m bs ys) = target --we're casing down here so we're lazy in target
        (_likes, _rL, remRight) = likeTerms (ZeroVar n as) (ZeroVar m bs)
    countToMapTo <- (remRight <> Count 0 Empty ys) `divCount` k 
    let updateMap = one (x, countToMapTo)
        updatedF = updateCount updateMap f 
        updatedS = updateCount updateMap s
        msg = "updated " <> showP (f, s) 
          <> " to match " <> showP target 
          <> " getting " <> showP (updatedF, updatedS)
    --trace msg $
    assert (updatedF == target) $ pure updatedS
  (Just f, s) -> if f == target then Just s else error ("failed to resolve: " <> showP (target, f, s))

--skipContainsVar :: Skip Count Bit -> Bool
thingContainsVar :: (Bifoldable p) => p Count b -> Bool
thingContainsVar = getAny . bifoldMap (Any . countContainsVar) (const mempty) where
    countContainsVar = \case
        FinCount _n -> False
        _notFin -> True


guessAndProveWhatHappensNext :: Turing -> SkipBook Bit -> Config Count Bit -> SymbolVar -> [(Skip Count Bit, SkipOrigin Bit)]
guessAndProveWhatHappensNext machine book startConfig varToGeneralize
  = --trace ("trying to guess what happens after:\n" <> show (pretty startConfig)) $
    mapMaybe getProof $ zipExact goodGuesses proofAttempts
  where
    guesses = --force $ 
      guessWhatHappensNext machine startConfig varToGeneralize
    goodGuesses = filter thingContainsVar guesses
    proofAttempts = --force $ 
      (\skip -> --force $ 
        proveInductively 200 machine book skip (BoundVar 0)) <$> goodGuesses
    getProof = \case
        (_, Left msg) -> --trace ("induction failed b/c:\n" <> show (pretty msg))
           Nothing
        (skip, Right origin) -> Just (skip, origin)

--takes a list of at least 2 pairs of counts, and returns a pair of counts that generalizes them,
-- if possible, in the sense that it has bound vars which can be subbed to be all the pairs
--algorithm: if each pair is equal, return said pair
-- else, if they share a common integer difference, return the function that applies that difference 
-- such as n + 2 -> n, or n -> n + 3
-- else, see if they are generated by a function of the form x -> m * x + b 
-- else give up 
generalizeFromCounts :: NonEmpty (Count, Count) -> Maybe (Count, Count)
generalizeFromCounts xs = --force $ 
  allEqualPair <|> additivePair <|> affinePair where
    allEqualPair :: Maybe (Count, Count)
    allEqualPair = guard (list1AllEqual xs) >> pure (head xs)
    countToMaybeNat = \case
        Count n Empty Empty -> Just n
        _ -> Nothing
    naturalPairs :: Maybe (NonEmpty (Natural, Natural))
    naturalPairs = let
        ans = traverse (bitraverse countToMaybeNat countToMaybeNat) xs
        msg = "attempting to generalize these pairs:\n" <> show ans
     in
        --trace msg 
        ans
    subNats :: Natural -> Natural -> Int
    subNats = (-) `on` fromIntegral
    differences = let
        ans = uncurry subNats <$$> naturalPairs
        msg = "differences were\n" <> show ans
      in
        --trace msg ans
        ans
    newBoundVarBad :: Count
    newBoundVarBad = newBoundVar 0
    --takes an integer and returns the count pair that represents a function that adds that to its input
    generalizeAddDiff :: Partial => Int -> (Count, Count)
    generalizeAddDiff d = --trace ("about to use " <> show d <> "\n") $ 
      case compare d 0 of
        --this means (x, y) x > y since d = x - y
        GT -> (newBoundVarBad <> finiteCount (fromIntegral d), newBoundVarBad)
        --this means (x, y) x < y
        LT -> (newBoundVarBad, newBoundVarBad <> finiteCount (fromIntegral $ -1 * d))
        EQ -> (newBoundVarBad, newBoundVarBad)
            --todo, right now we use this case in guessWhatComesNext but we probably shouldn't
            --error "generalizeAddDiff should not be called on a zero integer"
    additivePair :: Maybe (Count, Count)
    additivePair = differences >>= \case
        ds@(d1 :| _rest) -> guard (list1AllEqual ds) >> pure (generalizeAddDiff d1)
    conformsToAffine :: Natural -> Int -> (Natural, Natural) -> Bool
    conformsToAffine m b (x, y) = fromIntegral x * fromIntegral m + b == fromIntegral y
    generalizeMulDiff :: Natural -> Int -> (Count, Count)
    generalizeMulDiff m b =  if b >= 0
        then (newBoundVarBad, m `nTimes` newBoundVarBad <> finiteCount (fromIntegral b))
        --this is the line we need to change
        --note: x -> 2x - 1 is not the same as x + 1 -> 2x !!
        --so given 2x - 1 we compute the smallest multiple of 2 bigger than 1 (1), called toMul
        -- and then x + toMul is like subtracting 2 * toMul, so we have to add that back on the 
        --other side, except for the b we are actually supposed to subtract
        else let 
          toMul = 1 + fromIntegral (-b) `div` m
          --do subtraction in int space and then go back to natural space
          c = fromIntegral (fromIntegral (toMul * m) + b) 
          in 
          (newBoundVarBad <> finiteCount toMul, m `nTimes` newBoundVarBad <> finiteCount c)
    affinePair :: Maybe (Count, Count)
    affinePair = do 
      nps <- naturalPairs
      guard (length nps >= 3) 
      case nps of
        (_pair :| []) -> Nothing
        --going for x -> m * x + b - we assume m > 0 but b can be any integer
        -- does not handle x -> m * (x + a) + b - but probably could somehow?
        -- fails on (3,2), (4,1)
        pairs@((x1, y1) :| (x2, y2) : _rest) -> do
          --the idea here is we're going to subtract x1 from x2, and then divide by it, so it has to be strictly positive
          --while we're going to subtract y1 from y2 but not divide by it so it just has to be at least 0
            m <- if (x2 > x1) && (y2 >= y1)
                then (y2 - y1) `maybeDiv` (x2 - x1)
                else if (x1 > x2) && (y1 >= y2) 
                  then (y1 - y2) `maybeDiv` (x1 - x2)
                  else Nothing 
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

varNotUsedInSkip :: Skip Count s -> BoundVar 
varNotUsedInSkip skip = case S.lookupMax allInts of 
  Nothing -> BoundVar 0
  Just x -> BoundVar (x + 1)
  where 
  allInts = S.map getBoundVar allUsedVars 
  allUsedVars = bifoldMap countUsedVars (const mempty) skip 
  countUsedVars (Count _n _as xs) = keysSet xs 

chainArbitrary :: forall s. (Eq s, Pretty s) => Skip Count s -> Either Text (Skip Count s)
chainArbitrary skip@(Skip start end steps halts disp) = case end of 
  EndSide _ph _dir _xs -> Left "endside" --TODO we can probably handle this
  EndMiddle endConfig -> do 
    (newStart, newEnd) <- matchConfigs start endConfig 
    pure (Skip newStart (EndMiddle newEnd) Empty False Zero) --TODO handle steps obviously
  where 
  newVar :: BoundVar 
  newVar = varNotUsedInSkip skip 
  matchConfigs :: Config Count s -> Config Count s -> Either Text (Config Count s, Config Count s)
  matchConfigs c1@(Config ph ls p rs) c2@(Config ph2 xs q ys) = do 
    let rom = showP c1 <> " " <> showP c2 
    guardMsg (ph == ph2 && p == q) $ "phases or points not equal: " <> rom 
    (newLs, newXs) <- matchLists ls xs 
    (newRs, newYs) <- matchLists rs ys
    pure (Config ph newLs p newRs, Config ph newXs p newYs)
  matchLists :: [(s, Count)] -> [(s, Count)] -> Either Text ([(s, Count)], [(s, Count)])
  matchLists xs ys = do 
    --maybeRes :: Either Text [((s, Count), (s, Count))]
    maybeRes <- traverse (uncurry matchPairs) (zip xs ys) --zip discards longer 
    let leftover = case remainingLonger xs ys of 
          Left xs_left -> Start xs_left
          Right ys_left -> End ys_left
    applyLeftover (unzip maybeRes, leftover) 
  applyLeftover :: (([(s, Count)], [(s, Count)]), Leftover s) -> Either Text ([(s, Count)], [(s, Count)])
  applyLeftover ((starts, ends), lo) = case lo of 
    Start [] -> Right (starts, ends) 
    End [] -> Right (starts, ends)
    Start [(s, FinCount n)] -> Right (starts ++ [(s, boundVarCount newVar n)], ends)
    End [(s, FinCount n)] -> Right (starts, ends ++ [(s, boundVarCount newVar n)])
    _ -> Left $ "leftover was not a single finite thing: " <> showP lo 
  matchPairs :: (s, Count) -> (s, Count) -> Either Text ((s, Count), (s, Count))
  matchPairs (s, c) (t, d) = do 
    guardMsg (s == t) "two bits didn't match" 
    (c', d') <- matchCounts c d 
    pure ((s, c'), (t, d'))
  --first one is start, second one is end
  matchCounts :: Count -> Count -> Either Text (Count, Count)
  matchCounts c d = let rom = showP c <> " and " <> showP d in -- "rest of message" 
    if c == d then Right (c,d) else case (c,d) of 
      --if we have a pair of counts like (x + 2, x + 5), every trip through, we increase the output by 3 (increaseAmt)
      -- so the total increase is 3 * y, for a "newVar" y, and that is the output below. 
    (OneVar n as k x, OneVar m bs j y) -> do 
      guardMsg (x == y) $ "vars didn't match: " <> rom 
      guardMsg (k == 1 && j == 1) $ "vars weren't both 1: " <> rom
      increaseAmt <- failMsg "chaining didn't increase" $ subCountFromCount (ZeroVar m bs) (ZeroVar n as) 
      case increaseAmt of 
        (FinCount incNat) -> let base =  OneVar n as 1 x in Right (base, base <> boundVarCount newVar incNat)
        _ -> Left $ "amt of increase was not finite: " <> showP increaseAmt <> "\n" <> rom 
    _ -> Left $ "couldn't match counts:" <> rom 
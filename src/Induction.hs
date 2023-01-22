{-# LANGUAGE TupleSections #-}
module Induction where

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs, keysSet, keys)
import qualified Data.Map.Monoidal as MM
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S

import Prettyprinter
import Data.Either.Combinators hiding (rightToMaybe)

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
import Safe.Partial
import Data.Bifoldable (Bifoldable)

import qualified Relude.Unsafe as U

import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
import SimulationLoops
import Graphs
import TapeSymbol
import Data.Containers.ListUtils (nubOrd)

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
proveInductivelyIMeanIT :: (TapeSymbol s, HasCallStack) => Turing -> SkipBook s -> Steps
    -> TapeHist s InfCount -> ReadShiftHist
    -> (SkipBook s, Either Text (Skip Count s))
proveInductivelyIMeanIT machine book curStep hist rsHist
  = force $ let indGuess = guessInductionHypothesis hist rsHist in
  trace ("indGuess was: " <> showP indGuess) $ case indGuess of
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
proveStrong :: forall s. (TapeSymbol s, HasCallStack) => Int -> Turing -> SkipBook s
 -> Skip Count s -> BoundVar -> (SkipBook s, Either Text (SkipOrigin s))
proveStrong loopLim machine book goal indVar = swapEither <$> loop 0 book Nothing where
  -- the skiporigin is one for specifically the goal 
  -- the text is "we failed"
  loop :: Int -> SkipBook s -> Maybe (Config Count s) -> (SkipBook s, Either (SkipOrigin s) Text)
  loop idx curBook mbLastStuck = --force $ trace ("provestrong loop " <> show idx <> "\n") $
    if idx > loopLim then error "wow we exceeded looplim!" -- Right "limit exceeded" 
    else case proveInductively 110 machine curBook goal indVar of
      Right skipOrigin -> (curBook, Left skipOrigin)
      Left (msg, maybeStuckConfig) -> --trace ("provestrong stuck on:\n" <> show (pretty maybeStuckConfig) <> "\nbecause:\n" <> toString msg) $
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

--TODO: this is obviously a huge kludge. hopefully the smarter second version of the algorithm
--won't have this issue
proveInductively :: forall s. (HasCallStack, TapeSymbol s)
  => Int -> Turing -> SkipBook s
  -> Skip Count s -> BoundVar
  -> Either (Text, Maybe (Config Count s)) (SkipOrigin s)
proveInductively limit t book goal indVar
  = case proveInductivelyWithX 0 limit t book goal indVar of
    Right so -> Right so
    Left stuck -> case proveInductivelyWithX 1 limit t book goal indVar of
      Right so -> Right so
      Left _stuckAgain -> Left stuck --we want the first stuckness, not the second one, usually

{-
A function which is sort of like `proveInductively`, but it doesn't actually do induction.
It just brute simulates forward and sees if that works. This is good to be able to prove
things like the 1^n christmas tree that just goes back and forth and we already know it 
skips blocks of 1s so we can just simulate for a finite number of (big) steps.
-}
-- proveSimply :: Int -> Turing -> SkipBook Bit -> Skip Count Bit
  -- -> Either (Text, Maybe (Config Count Bit)) (SkipOrigin Bit)
-- proveSimply limit t book goal = undefined


--goal: make a thing that takes a skip that might apply to a certain machine, 
--attempts to simulate forward to prove that skip using induction
-- the first int is the "number to add to X" when trying to prove the indhyp. 
--it's a huge kludge and hopefully I can get rid of it soon
-- the second int is the limit on the number of steps to take before giving up 
--the (skip bit) input is the goal to be proven, 
-- the BoundVar is the variable on which we are going to do induction
--returns Left with an error message, and the config we got stuck on 
--or Right with success

proveInductivelyWithX :: forall s. (HasCallStack, TapeSymbol s)
  => Natural -> Int -> Turing -> SkipBook s
  -> Skip Count s -> BoundVar
  -> Either (Text, Maybe (Config Count s)) (SkipOrigin s)
proveInductivelyWithX xPlus limit t book goal indVar = let
  ans =  -- <> "using book\n" <> show (pretty book)) $
    case baseCase of
      Left res -> Left $ first ("failed base: " <>) res
      Right _ -> case indCase of
        Left res -> Left $ first ("failed ind: " <>) res
        Right _ ->  pure origin
  msg = ("trying to prove:\n" <> show (pretty goal))
          <> "\n inducting on:" <> show indVar
          <> "\ngot res" <> showP ans <> "\nEOM\n"
    in
     --force $
     --trace msg $
       assertMsg (isSameInAsOut goal && thingContainsVar goal) (fromString msg)
       ans
    where
    origin :: SkipOrigin s
    origin = Induction book limit
    baseCase :: Either (Text, Maybe (Config Count s)) Natural
    baseCase = proveSimLinearAndTree limit limit t book baseGoal
    baseGoal :: Skip Count s
    baseGoal = replaceVarInSkip goal indVar $ finiteCount 1 --TODO, should be 1
    setStepCount steps skip = skip & hops .~ FinCount steps
    goalPlusX x = setStepCount (120 + x) $
      replaceVarInSkip goal indVar $ FinCount x <> symbolVarCount newSymbolVar 1
    indCase :: Either (Text, Maybe (Config Count s)) Natural
    --this doesn't actually add the inductive hypothesis to the book!
    indCase = --trace "\nstarting ind\n" $ 
      --deepseq indHyp $
        proveSimLinearAndTree limit limit t
         (addSkipToBook indHyp InductionHypothesis book)
         indGoal
    indHyp :: Skip Count s
    indHyp = let
        --TODO: make the hypothesis be 0 and the goal be 1 again
        ans = goalPlusX xPlus
        msg = "indHyp is:\n" <> show (pretty ans)
      in
        -- $ trace msg
        ans
      --there's one machine that needs this to be 1 and one which needs it to be 2
    indGoal :: Skip Count s
    indGoal = goalPlusX (xPlus + 1)
    newSymbolVar :: SymbolVar --TODO: this is obviously incredibly unsafe
    newSymbolVar = SymbolVar 0

--first int is linear step limit, second int is tree step limit
proveSimLinearAndTree :: (HasCallStack, TapeSymbol s) => Int -> Int -> Turing -> SkipBook s
  -> Skip Count s -> Either (Text, Maybe (Config Count s)) Natural
-- simulateViaDFS :: Int -> Int -> SkipBook Bit -> Skip Count Bit -> Either Text Natural 
proveSimLinearAndTree linStep treeStep machine book skip
  =
    --force $ 
  --trace ("--------\n\n\n\n\n-----------\ntrying to prove: " <> showP skip) $
  --TODO: why is it linStep treeStep fed as the limits to simulateViaDFS
  --a node in DFS is a big step, so the nat output here is a big step
  case simulateViaDFS linStep treeStep book skip of
    Right nat -> Right nat
    Left text -> --trace (toString $ "dfs failed because:" <> text) $
     case proveBySimulating (fromIntegral linStep) machine book skip of
      --works if you comment out this error and return right, but HOW COULD THAT BE TRUE you should never hit this error
      --the reason for this is simulateViaDFS should guess the same as proveBySimulating as it's first deep path, and should only recurse onto 
      --other paths if that doesn't work
      --but if proveBySimulating returns success, it seems to work, which is a contradiction
      --oh dear, maybe part of the issue is whether "simulateViaDFS" and "proveBySimulating" are using "big steps" or "little steps"? 
      --because the error occurs with count=467 which seems to be bigger than the callsite (guessAndProveWhatHappensNext), 
      --which calls with a limit of 200 afaict 

      --update 10 July: it seems like the error has to be that "maximum" and "sortBy flip" are somehow not producing the same thing, 
      --or something dumb like that, I can't see what else would produce this behavior
      --I investigated a bit more and this seems likely to be true, yes. there are two skips with value "100" 
      --and they are probably just randomly applied in different orders for no particularly good reason
      --steps here is a big step
      Right steps -> error $ "what? steps: " <> showP steps <> " linstep:" <> showP linStep <> " treestep: " <> showP treeStep
                            <> "\nmachine was\n" <> showP machine <> "\nwe were proving:\n" <> showP skip
                            <> "\ndfs failed because:" <> text
                            -- <> "\nbook was:\n" <> showP book
      res@(Left _) -> res

-- given a skip, replaces all occurences of a particular BoundVar with a particular Count
replaceVarInSkip :: Skip Count s -> BoundVar -> Count -> Skip Count s
replaceVarInSkip (Skip sConfig eSE hopCount) varIn countOut =
    Skip newConfig newSE (replaceVarInCount hopCount) where
    newConfig = replaceVarInConfig sConfig
    newSE = replaceVarInSE eSE
    replaceVarInConfig (Config p ls c_point rs)
        = Config p
        (replaceVarInList ls)
        c_point
        (replaceVarInList rs)
    replaceVarInTape (ExpTape ls p rs)
        = ExpTape
        (replaceVarInList ls)
        p
        (replaceVarInList rs)
    replaceVarInTP = \case
        Middle tape -> Middle $ replaceVarInTape tape
        Side d xs -> Side d $ replaceVarInList xs
    replaceVarInSE = \case
      SkipStepped p tp -> SkipStepped p $ replaceVarInTP tp
      SkipHalt tp -> SkipHalt $ replaceVarInTP tp
      other -> other
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
-- output natural is the number of steps it actually took 
-- the text tells you why you failed, and you might have failed via getting "stuck" on something, in which case we return that
-- this linearly simulates forward, which sometimes gets you into a hole when you prove something that skips ahead, because 
-- you can end up skipping past the thing you want. to solve this problem, I wrote simulateviadfs
proveBySimulating :: forall s. (TapeSymbol s) => Natural -> Turing -> SkipBook s
  -> Skip Count s -> Either (Text, Maybe (Config Count s)) Natural
proveBySimulating limit t book (Skip start skipEnd _) = case skipEnd of
  SkipHalt _ -> Left ("can't prove halt by induction", Nothing)
  SkipUnknownEdge _ -> Left ("can't prove unknownedge by induction", Nothing)
  SkipNonhaltProven _ -> Left ("can't prove nonhalt by induction", Nothing)
  SkipStepped ph tp -> let
    ans = loop 0 (start ^. cstate) (second NotInfinity $ configToET start ^. _2) (finiteCount 0)
    msg = "starting pos:\n" <> show (pretty start) <> "\nsucceeded: " <> show (has _Right ans)
        <> "\nans:" <> showP ans
    in
--    force $ 
--    trace msg
    ans where
    -- four conditions: we've taken more steps than the limit,
    -- we've succeeded, stepping fails for some reason, or we continue 
    loop :: Natural -> Phase -> ExpTape s InfCount -> Count -> Either (Text, Maybe (Config Count s)) Natural
    loop numSteps p tape curCount
        -- | trace (Unsafe.init $ toString $ "PS: steps:" <> show numSteps <> " count:" <> showP curCount <>
        --            " p:" <> dispPhase p <> " tape is: " <> dispExpTape tape) False = undefined
      --we have to check the limit before checking for success, 
      --because we don't want to succeed in 101 steps if the limit is 100 steps
      | numSteps > limit = Left ("exceeded limit of " <> show limit <> " while simulating", Nothing)
      | indMatch p tape (ph, tp) = pure numSteps
      | otherwise = case skipStep undefined t book p tape of
            Unknown e -> Left ("hit unknown edge" <> show e, Nothing)
            Stopped {} -> Left ("halted while simulating", Nothing)
            NonhaltProven {} -> Left ("went forever while simulating", Nothing)
            MachineStuck -> let
                stuckConfig = etToConfig p $ second deInfCount tape
                msg = "machine stuck on step: " <> show numSteps
                  <> " in phase:" <> show p
                  <> "\ncur tape:" <> dispExpTape tape
                  <> "\ngoal:" <> show (pretty (ph, tp)) <> "\nend of goal"
                in
                Left (msg, Just stuckConfig)
            Stepped Infinity _ _ _ _ _ -> Left ("hopped to infinity", Nothing)
            Stepped (NotInfinity hopsTaken) newPhase newTape skipUsed _ _
                -> --trace ("used skip: " <> showP skipUsed)
                loop (numSteps + 1) newPhase newTape (curCount <> hopsTaken)
    indMatch :: Phase -> ExpTape s InfCount -> (Phase, TapePush Count s) -> Bool
    indMatch cur_p et (goalPh, goalTP) = case secondT mbdeInfCount et of
        Nothing -> False
        Just tape@(ExpTape ls point rs) -> case goalTP of
            Middle (ExpTape goal_ls goal_p goal_rs)
                -> cur_p == goalPh && ls == goal_ls && point == goal_p && rs == goal_rs
            Side dir xs -> endSideTapeMatch dir xs tape &&
                endSideTransMatch dir goalPh t cur_p tape
      where
        endSideTapeMatch :: Dir -> [(s, Count)] -> ExpTape s Count -> Bool
        endSideTapeMatch L goal (ExpTape _ls point rs) = case getNewFinPoint goal of
            Nothing -> False
            Just (goal_p, goal_xs) -> goal_p == point && goal_xs == rs --yes this is reversed
        endSideTapeMatch R goal (ExpTape ls point _rs) = case getNewFinPoint goal of
            Nothing -> False
            Just (goal_p, goal_xs) -> goal_p == point && goal_xs == ls --yes this is reversed
        endSideTransMatch :: Dir -> Phase -> Turing -> Phase ->  ExpTape s Count -> Bool
        endSideTransMatch goal_d goalPhase (Turing _n map) curPhase (ExpTape _ p _)
            = case map ^. at (curPhase, getPoint p) of
                Nothing -> False
                (Just Halt) -> goal_d == L
                (Just (Step transPhase _bit d)) -> goal_d == d && goalPhase == transPhase
        mbdeInfCount Infinity = Nothing
        mbdeInfCount (NotInfinity c) = Just c

getAllVars :: Bifoldable p => p Count b -> Set BoundVar
getAllVars = fromList . bifoldMap getCountVars (const []) where
  getCountVars (Count _n _as xs) = toList $ keys xs

--TODO, it's really dumb we have to "deInfCount here"
getNextConfigs :: forall s. (TapeSymbol s)
  => SkipBook s -> Config Count s -> [Config Count s]
getNextConfigs book curConfig = f ans
 where
  f = id -- trace msg
  msg = "next possible configs:\n" <> foldMap (\x -> showP x <> "\n") ans
          <> "skips used: " <> foldMap (\x -> showP x <> "\n") skipsUsed
          <> "available book skips: " <> foldMap (\x -> showP x <> "\n")
              (filter (\skip -> length (getAllVars skip) > 1) $ getSkipsFromBook book)
          <> "\n"
  skipsUsed = mapMaybe getSkip choices
  ans =  first deInfCount <$> mapMaybe getConfig choices
  getConfig :: PartialStepResult InfCount s -> Maybe (Config InfCount s)
  getConfig = \case
    Stepped _ ph newTape _ _ _ -> Just $ etToConfig ph newTape
    _ -> Nothing
  getSkip ::  PartialStepResult InfCount s -> Maybe (Skip Count s)
  getSkip = \case
    Stepped _ _ _ skip _ _ -> Just skip
    _ -> Nothing
  choices :: [PartialStepResult InfCount s]
  --flip since sort gives smallest to largest by default but we want the largest skip first
  choices = sortBy (flip skipPrecedence)
    $ snd <$> uncurry (getSkipsWhichApply undefined book) (configToET $ first NotInfinity curConfig)

--the text is why you failed, and the natural is how many big steps 
simulateViaDFS :: (TapeSymbol s) => Int -> Int -> SkipBook s -> Skip Count s
  -> Either Text Natural
simulateViaDFS stepLim depthLim book (Skip startConfig skipEnd _hops)
  = case res of
  Right (Success vs) -> Right $ fromIntegral $ length vs
  --the problem here is we sort of want some kind of like 'what did the DFS get stuck on' list 
  --but that's not something we have right now
  Right (NoSuccess numNodes) -> Left $ "dfs exhaustively searched " <> show numNodes <> " nodes with no results"
  Left message -> Left $ "failed dfs: " <> message
  where
    target = case skipEnd of
      SkipStepped ph (Middle et) -> Just $ etToConfig ph et
      _ -> Nothing
    res = case target of
      Nothing -> Left "target skip did not endmiddle"
      Just endConfig -> dfs stepLim depthLim (getNextConfigs book) (== endConfig) startConfig

transposeNE :: NonEmpty [a] -> [NonEmpty a]
transposeNE (x :| xs) = assertMsg (all (\y -> length y == length x) xs) ("not all same length: " <> showP (length x, length <$> xs))
  getZipList $ (:|) <$> ZipList x <*> ZipList (transpose xs)

transposeOverPair :: forall a. NonEmpty ([a], [a]) -> ([NonEmpty a], [NonEmpty a])
transposeOverPair xs = bimapBoth transposeNE $ NE.unzip xs

transposeOverTwoPairs :: NonEmpty (([a], [a]), ([a], [a])) -> (([NonEmpty a], [NonEmpty a]), ([NonEmpty a], [NonEmpty a]))
transposeOverTwoPairs xs = bimapBoth (bimapBoth transposeNE) $ bimapBoth NE.unzip $ NE.unzip xs

test :: NonEmpty [a] -> [NonEmpty a]
test = sequenceA

bifoldMapBoth :: (Bifoldable p, Monoid m) => (a -> m) -> p a a -> m
bifoldMapBoth f = bifoldMap f f

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

possibleSignatures :: forall s. (Ord s, Pretty s)
  => [(Phase, ExpTape s InfCount)] -> [(Phase, Signature s)]
possibleSignatures hist = let ans = filter (\s -> sigFreqs ^?! ix s >= 3) tapeSignatures in
    -- trace (toString $ "possible sigs were:\n" <> T.intercalate "\n\n\n" $ (\s -> showP s <> "\n" 
    --     <> showP (filter (\(p, t) -> (p, tapeSignature t) == s) hist)) 
    --     <$> filter (\(_p, sig) -> signatureComplexity sig <= 3) ans) 
    ans
  where
    tapeSignatures :: [(Phase, Signature s)]
    tapeSignatures = tapeSignature <$$> hist
    sigFreqs :: Map (Phase, Signature s) Int
    sigFreqs = --trace ("tapesigs" <> showP (filter (\(_, s) -> signatureComplexity s <= 4) tapeSignatures))
      M.fromListWith (+) $ (,1) <$> tapeSignatures

simplestNSigs :: Natural -> [(Phase, ExpTape Bit InfCount)] -> [(Phase, Signature Bit)]
simplestNSigs n hist = take (fromIntegral n) $
    sortBy (compare `on` signatureComplexity . snd) $
    possibleSignatures hist

--pick a signature by simplest, then by 
orderSignatures :: (Ord s) => Signature s -> Signature s -> Ordering
orderSignatures s t = case (compare `on` signatureComplexity) s t of
  LT -> LT
  GT -> GT
  EQ -> case (compare `on` leftLen) s t of
    LT -> LT
    GT -> GT
    EQ -> (compare `on` rightLen) s t
      -- case (compare `on` rightLen) s t of 
      -- LT -> LT 
      -- GT -> GT 
      -- EQ -> (flip compare `on` getP) s t
  where
    getP (Signature _ls p _rs) = p
    leftLen (Signature ls _p _rs) = length ls
    rightLen (Signature _ls _p rs) = length rs

orderPhaseSigPairs (ph1, s) (ph2, t) = case orderSignatures s t of
  LT -> LT
  GT -> GT
  EQ -> compare ph1 ph2

--given a history, guesses a "critical configuration" 
-- a simple tape appearance the machine repeatedly returns to
guessCriticalConfiguration :: (Ord s, Show s, Pretty s) => [(Phase, ExpTape s InfCount)] -> Either Text (Phase, Signature s)
guessCriticalConfiguration hist = case possibleSignatures hist of
  [] -> Left "no possible criticalconfigs"
  xs ->
    --trace ("possible sigs: " <> showP (nubOrd (filter (\x -> signatureComplexity (snd x) <= 5) xs))) $
    Right $ minimumBy orderPhaseSigPairs xs --(orderSignatures `on` snd) xs

-- given a particular config, return the list of times that config occurred, plus the integer position in the original list
obtainConfigIndices :: (Eq s) => [(Phase, ExpTape s InfCount)] -> (Phase, Signature s)
    -> [(Int, (Phase, ExpTape s InfCount))]
obtainConfigIndices hist config
    = filter (\(_, (p, tape)) -> (p, tapeSignature tape) == config) $ zip [0, 1 .. ] hist

--given a tape history and a readshift history corresponding to what was read at each 
--transition, plus two indicies, obtain the slices that were read + written from the 
--beginning to the end
getReadShiftSlicePair :: (Partial, Eq s, Pretty s) => [(Phase, ExpTape s InfCount)] -> [ReadShift] -> Int -> Int
  -> (ExpTape s Count, ExpTape s Count)
getReadShiftSlicePair hist rSs start end = --trace ("lengths: " <> show (length hist, length rSs) <> " s,e: " <> show (start,end))
 (startSlice, endSlice) where
    startTape = hist ^?! ix start . _2
    endTape = hist ^?! ix end . _2
    rsSlice = if start == end then [] else (slice start (end-1) rSs)
    (ReadShift lenL lenR shiftDist) = mconcat rsSlice
    startSlice = sliceExpTape startTape lenL lenR
    --because if you go 5 steps right, you need to slice 5 less distance to the right and
    --5 more distance left
    endSlice = sliceExpTape endTape (lenL - shiftDist) (lenR - shiftDist)

getReadShiftSlicePairC :: (Eq s, Pretty s) => [(Phase, ExpTape s Count)] -> [ReadShift] -> Int -> Int -> (ExpTape s Count, ExpTape s Count)
getReadShiftSlicePairC hist = getReadShiftSlicePair ((fmap $ fmap $ second NotInfinity) hist)

--given a list of displacements and a start and end index, return the maximum 
--left and rightward displacements that occured between the two indices, inclusive 
maximumDisplacement :: Partial => [Int] -> Int -> Int -> (Int, Int)
maximumDisplacement ds start end = --trace ("s " <> show start <> " e " <> show end <> "  ds:\n" <> show ds) $
 let d_len = length ds in
    assert (start <= end && start <= d_len && end <= d_len)
    (minimum portion, maximum portion) where
      portion = slice start end ds

getSlicePair'' :: Partial
  => ExpTape Bit Count
  -> ExpTape Bit Count
  -> [Int] -> Int -> Int
  -> (ExpTape Bit Count, ExpTape Bit Count)
getSlicePair'' sT eT = getSlicePair' (second NotInfinity sT) (second NotInfinity eT)

getSlicePair' :: (Partial, Eq s)
  => ExpTape s InfCount
  -> ExpTape s InfCount
  -> [Int] -> Int -> Int
    -> (ExpTape s Count, ExpTape s Count)
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
getSlicePair :: (Eq s) => [(Phase, ExpTape s InfCount)] -> [Int] -> Int -> Int
  -> (ExpTape s Count, ExpTape s Count)
getSlicePair hist disps start end = getSlicePair' startTape endTape disps start end where
    startTape = hist ^?! ix start . _2
    endTape = hist ^?! ix end . _2

getSlicePairC :: (Eq s) => [(Phase, ExpTape s Count)] -> [Int] -> Int -> Int -> (ExpTape s Count, ExpTape s Count)
getSlicePairC hist = getSlicePair $ (fmap $ fmap $ second NotInfinity) hist

--says whether by dropping one or both the left or the right bits of the start sig, we can reach the end sig
--but we also want to be willing to drop one or both of the left or the right bits of the end sig
--but on one side, we can drop either the start or the end, but not both
data Drop = NoDrop | StartDrop | EndDrop deriving (Eq, Ord, Show, Generic)

calcCommonSig :: (Eq s) => Signature s -> Signature s -> Maybe (Drop, Drop)
calcCommonSig (Signature ls1 p1 rs1) (Signature ls2 p2 rs2) = -- trace ("commonsig-ing " <> show start <> " and " <> show end) $
  asum $ check <$> drops <*> drops where
    drops = [NoDrop, StartDrop, EndDrop]
    check :: Drop -> Drop -> Maybe (Drop, Drop)
    check dl dr = do
      (ls1', ls2') <- dropFunc dl (ls1, ls2)
      (rs1', rs2') <- dropFunc dr (rs1, rs2)
      let newStart = Signature ls1' p1 rs1'
          newEnd = Signature ls2' p2 rs2'
      if newStart == newEnd then Just (dl, dr) else Nothing
    dropFunc :: Drop -> ([s], [s]) -> Maybe ([s], [s])
    dropFunc = \case
      NoDrop -> pure
      StartDrop -> firstT dropList
      EndDrop -> secondT dropList
    dropList = viaNonEmpty init


--if we have to drop one or both of of the end bits of the start signature, then to compensate we will add
--a zero to the end signature in the places we drop the bits 
addZeros :: (Drop, Drop) -> (([Count], [Count]), ([Count], [Count]))
                         -> (([Count], [Count]), ([Count], [Count]))
addZeros (dl, dr) ((s_ls, s_rs), (e_ls, e_rs)) = let
    (s_ls', e_ls') = addFunc dl (s_ls, e_ls)
    (s_rs', e_rs') = addFunc dr (s_rs, e_rs)
   in
    ((s_ls', s_rs'), (e_ls', e_rs'))
   where
    appendZero xs = xs <> [Empty]
    --you reverse start is first and end is second
    --because you are adding a zero. so if we dropped something from the start, then we 
    --want to add a zero to the end. 
    addFunc :: Drop -> ([Count], [Count]) -> ([Count], [Count])
    addFunc = \case
      NoDrop -> id
      StartDrop -> second appendZero
      EndDrop -> first appendZero

--I have no idea how to write this function
generalizeFromExamples :: [(ExpTape Bit Count, ExpTape Bit Count)] -> Maybe (Skip Count Bit)
generalizeFromExamples slicePairs = undefined


obtainCriticalIndicesConfigs :: (TapeSymbol s) => TapeHist s InfCount
  -> Either Text (Phase, [(Int, (Phase, ExpTape s InfCount))])
obtainCriticalIndicesConfigs (TapeHist hist) = do
  criticalConfig@(criticalPhase, _criticalSignature) <- guessCriticalConfiguration hist
  let
    configIndicesAndConfigs = let ans = obtainConfigIndices hist criticalConfig in
      --trace ("configs were:\n" <> showP ans)
      ans
  pure (criticalPhase, configIndicesAndConfigs)

guessInductionHypothesis :: (TapeSymbol s) => TapeHist s InfCount -> ReadShiftHist
  -> Either Text (Skip Count s)
guessInductionHypothesis th rsh = force $ do
  (criticalPhase, configIndicesAndConfigs) <- obtainCriticalIndicesConfigs th
  let
    indGuess = case guessInductionHypWithIndices th rsh criticalPhase configIndicesAndConfigs of
      Right ans -> Right ans
      --this is hacky and bad but it used to be necessary to guess right on trickyChristmasTree so I'll try it for now
      --24 jul 22  update is that it is no longer necessary, so I got rid of it, but we'll see what 
      --happens in the future
      --17 jan 23 I put it back and don't remember why
      Left msg -> --trace (toString $ "ind m1: " <> msg)
        guessInductionHypWithIndices th rsh criticalPhase (Unsafe.tail $ Unsafe.tail configIndicesAndConfigs)
    msg = "guessed indhyp:\n" <> showP indGuess
    in

     --trace (toString msg) $
     warnMsg ((thingContainsVar <$> indGuess) /= Right False) msg
     indGuess

type FunctionExamples = (NonEmpty (Count, Count), (Maybe Count, Maybe Count))
data FlipFE = NoFlip | Flip deriving (Eq, Ord, Show, Generic)

flipFEs :: (FunctionExamples, FunctionExamples) -> (FunctionExamples, FunctionExamples)
flipFEs ((fromCl, (mFI, mFO)), (toCL, (mTI, mTO)))
 = ((flipPair <$> fromCl, (mFO, mFI)), (flipPair <$> toCL, (mTO, mTI)))
  where flipPair (a, b) = (b, a)

{- goal is to get a and x to be equal 
and to modify b and y as necessary for that to happen
to do that, we're going to map a and x to likes <> aLeft <> xLeft

example: (x, 3x) (x+1, 2x+1) -> (x+1, 3x+3), (x+1, 2x+1)
-}
squareUpPairs :: (Count, Count) -> (Count, Count) -> ((Count, Count), (Count, Count))
squareUpPairs (a, b) (x, y) = case likeTerms a x of
  (_likes, Empty, Empty) -> ((a, b), (x, y))
  (_likes, Empty, xLeft) -> case a of
    --x is strictly bigger, so we need to get a var out of a and 
    OneVar _n _as k v -> case xLeft `divCount` k of
      Nothing -> fail
      Just addToV -> let
        map = one (v, NotInfinity (addToV <> boundVarCount v 1))
        ans = first (bimapBoth $ partiallyUpdateCount map) ((a, b), (x, y))
        msg =  "inp was: " <> showP ((a,b), (x, y)) <> " ans was: " <> showP ans
        in assertMsg (uncurry (==) $ bimapBoth fst ans) msg ans
    _ -> fail
  (_likes, _aLeft, Empty) -> swap $ squareUpPairs (x, y) (a, b)
  (_likes, aLeft@(ZeroVar _ _), xLeft@(ZeroVar _ _)) -> case MM.assocs $ bound a of
    [] -> fail
    [(v, Sum i)] -> case (aLeft `divCount` i, xLeft `divCount` i) of
      (Just addA, Just addX) -> let
        map = one (v, NotInfinity $ addA <> addX)
        ans = bimapBoth (bimapBoth $ partiallyUpdateCount map) ((a, b), (x, y))
        in assert (uncurry (==) $ bimapBoth fst ans) ans
      _ -> fail
    _ -> fail
  (_likes, _aLeft, _xLeft) -> fail
  where
    fail = error $ "failed to square: " <> showP ((a, b), (x, y))
generalizeNumberSquare :: ([NonEmpty (Count, Count)], [NonEmpty (Count, Count)])
  -> Either Text ([(Count, Count)], [(Count, Count)])
generalizeNumberSquare ns = case bitraverseBoth (traverse generalizeFromCounts) ns of
  Right ans -> Right ans
  Left _msg -> --trace ("first generalized: " <> showP firstGeneralized) 
    first U.head $ collectEithers $ collectAns . generalizeAllPairs . allEqualEverything <$> firstGeneralized
  where
  collectEithers :: [Either a b] -> Either [a] b 
  collectEithers = foldr (\new accum -> case accum of 
    Right b -> Right b 
    Left as -> case new of 
      Right b -> Right b 
      Left a -> Left (a : as)) (Left [])
  myGeneralize countPairs = case generalizeFromCounts countPairs of
    Right (inC, outC) -> (Just inC, Just outC)
    Left _msg -> (Nothing, Nothing)
  --todo: I'd like to make partiallyGeneralized instead something where you generalize 
  --exactly one pair, rather than all of them. 
  partiallyGeneralized :: ([FunctionExamples], [FunctionExamples])
  partiallyGeneralized = bimapBoth (fmap (\cps -> (cps, myGeneralize cps))) ns
  possibleFirstGeneralize :: [ReifiedLens' ([FunctionExamples], [FunctionExamples]) FunctionExamples]
  possibleFirstGeneralize = (composeLenses _1 <$> lsOptics) ++ (composeLenses _2 <$> rsOptics)
    where
    lsOptics = mkLens <$> [0,1.. length (fst zeroGeneralized)-1]
    rsOptics = mkLens <$> [0,1.. length (snd zeroGeneralized)-1]
    mkLens :: Int -> ReifiedLens' [FunctionExamples] FunctionExamples
    mkLens i = Lens $ ixListLens i
  genOne :: FunctionExamples -> FunctionExamples
  genOne (countPairs, (_u,_v))= (countPairs,) $ case generalizeFromCounts countPairs of
    Right (inC, outC) -> (Just inC, Just outC)
    Left _msg -> (Nothing, Nothing)
  zeroGeneralized = bimapBoth (fmap (, (Nothing, Nothing))) ns
  firstGeneralized :: [([FunctionExamples], [FunctionExamples])]
  firstGeneralized = (\(Lens lens) fesPair -> fesPair & lens %~ genOne) <$>
    possibleFirstGeneralize <*> pure zeroGeneralized
  --right now this works on the first thing. we'll make it more general in a sec ok man
  generalizeBitAgainstOtherBit :: (FunctionExamples, FunctionExamples)
    -> (FunctionExamples, FunctionExamples)
  generalizeBitAgainstOtherBit inp@(lh@(fromCL, (Just fromIn, Just fromOut)),
                                       (toCL, (Nothing, mbToOut)))
    = --trace ("genrealizing: " <> showP fromCL <> "and" <> showP toCL) $
      case generalizeFromCounts (neZipExact (fst <$> fromCL) (fst <$> toCL)) of
      Left msg -> --trace (toString $ "failed: " <> msg) 
        inp
      Right (toFromCount, toCount) -> let
        ((newFromIn, newFromOut), (newToFrom,newToCount)) = squareUpPairs (fromIn, fromOut) (toFromCount, toCount)
        in
          assert (newFromIn == newToFrom)
            ((fromCL, (Just newFromIn, Just newFromOut)),
              (toCL, (Just newToCount, mbToOut)))
  generalizeBitAgainstOtherBit notGeneralizeable = notGeneralizeable

  generalizeBitBitWithFlip fe inp = case fe of
    NoFlip -> generalizeBitAgainstOtherBit inp
    Flip -> flipFEs (generalizeBitAgainstOtherBit (flipFEs inp))


  --apply this
  genAllEqual :: NonEmpty Count -> Maybe Count
  genAllEqual cl = if list1AllEqual cl then Just (head cl) else Nothing
  generalizeAllEqual :: FunctionExamples -> FunctionExamples
  generalizeAllEqual (cpl, pair) = case pair of
    (Nothing, Nothing) -> (cpl, (genAllEqual (fst <$> cpl), genAllEqual (snd <$> cpl)))
    (Just _, Just _) -> (cpl, pair)
    (_, _) -> error "generalizeAllEqual invariant"
  allEqualEverything :: ([FunctionExamples], [FunctionExamples])
    -> ([FunctionExamples], [FunctionExamples])
  allEqualEverything = bimapBoth (fmap generalizeAllEqual)

  --now we need to run generalizeBitAgainstOtherBit on all possible pairs of bits
  --and then we need to do that again in a loop until we hit a fixpoint and return the result
  --laterphina realized you only have to run it once, because if it's possible to solve the grid
  --with current methods, then you can solve it on the first go-round
  composeLenses :: Lens' s a -> ReifiedLens' a b -> ReifiedLens' s b
  composeLenses a (Lens b) = Lens $ a . b

  generalizeFromList :: [FunctionExamples] -> [ReifiedLens' [FunctionExamples] FunctionExamples]
  generalizeFromList fexs = mapMaybe mkLens $ zip [0,1..] fexs where
    mkLens (i, (_cl, (c1, c2))) = case (c1, c2) of
      (Just _, Just _) -> Just $ Lens $ ixListLens i
      _ -> Nothing

  eligibleGeneralizeFrom :: ([FunctionExamples], [FunctionExamples])
    -> [ReifiedLens' ([FunctionExamples], [FunctionExamples]) FunctionExamples]
  eligibleGeneralizeFrom (ls, rs)
    = (composeLenses _1 <$> lsOptics) ++ (composeLenses _2 <$> rsOptics)
    where
    lsOptics = generalizeFromList ls
    rsOptics = generalizeFromList rs

  generalizeToList :: [FunctionExamples] -> [(FlipFE, ReifiedLens' [FunctionExamples] FunctionExamples)]
  generalizeToList fexs = catMaybes $ bind mkLenses $ zip [0,1..] fexs where
    mkLenses (i, (_cl, (c1, c2))) = case (c1, c2) of
      (Nothing, _) -> [Just (NoFlip, Lens $ ixListLens i)]
      (_, Nothing) -> [Just (Flip, Lens $ ixListLens i)]
      _ -> [Nothing]

  eligibleGeneralizeTo :: ([FunctionExamples], [FunctionExamples])
    -> [(FlipFE, ReifiedLens' ([FunctionExamples], [FunctionExamples]) FunctionExamples)]
  eligibleGeneralizeTo (ls, rs)
    = (second (composeLenses _1) <$> lsOptics) ++ (second (composeLenses _2) <$> rsOptics)
    where
    lsOptics = generalizeToList ls
    rsOptics = generalizeToList rs

  generalizeTwoBitsGivenLens :: ReifiedLens' ([FunctionExamples], [FunctionExamples]) FunctionExamples
   -> (FlipFE, ReifiedLens' ([FunctionExamples], [FunctionExamples]) FunctionExamples)
   -> ([FunctionExamples], [FunctionExamples]) -> ([FunctionExamples], [FunctionExamples])
  generalizeTwoBitsGivenLens (Lens from) (fe, Lens to) stuff
    = stuff & combinedLens %~ generalizeBitBitWithFlip fe where
      combinedLens = from /\ to
  generalizeAllPairs :: ([FunctionExamples], [FunctionExamples])
    -> ([FunctionExamples], [FunctionExamples])
  generalizeAllPairs inp = let
    froms = eligibleGeneralizeFrom inp
    tos = eligibleGeneralizeTo inp
    genFuncs = generalizeTwoBitsGivenLens <$> froms <*> tos
    in
    foldr (\func fe -> func fe) inp genFuncs

  collectList :: [FunctionExamples] -> Either Text [(Count, Count)]
  collectList = traverse (\(cl, (mbC1, mbC2)) -> case (mbC1, mbC2) of
    (Just c1, Just c2) -> Right (c1, c2)
    _ -> Left ("failed to generalize: " <> showP cl <> "\ngot: " <> show (mbC1, mbC2))
    )
  collectAns :: ([FunctionExamples], [FunctionExamples])
    -> Either Text ([(Count, Count)], [(Count, Count)])
  collectAns = bitraverseBoth collectList

guessInductionHypWithIndices :: (Pretty s, Eq s, Show s, Partial)
  => TapeHist s InfCount -> ReadShiftHist -> Phase -> [(Int, (Phase, ExpTape s InfCount))]
  -> Either Text (Skip Count s)
guessInductionHypWithIndices (TapeHist hist) (ReadShiftHist rsHist)
                              criticalPhase configIndicesAndConfigs =
  let
    configIndices = let ans = fst <$> configIndicesAndConfigs in
      --trace ("configIndices were: " <> showP ans)
      ans
    indexPairs = zipExact (U.init configIndices) (U.tail configIndices)
    slicePairs = let ans = uncurry (getReadShiftSlicePair hist rsHist) <$> indexPairs in
      --trace ("slicepairs were:\n" <> showP ans)
      ans
    allSigs = let ans = fmap (bimapBoth tapeSignature) slicePairs in
      --trace ("allsigs were: " <> showP ans) 
      ans
  in do
  guardMsg (length configIndices >= 3) "less than 3 examples of the thing happening"
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
    augCountPairPairs = fmap (addZeros toDrop) countListPairPairs
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
  allThingsGeneralized <- generalizeNumberSquare thingsToGeneralizeList
  pure $ assembleSkip allThingsGeneralized criticalPhase (startSig, endSig)

assembleSkip :: (Pretty s, Show s) => ([(Count, Count)], [(Count, Count)]) -> Phase -> (Signature s, Signature s)
  -> Skip Count s
assembleSkip countPairListPair phase (startSig, endSig)= let
  startCounts = bimapBoth (fmap fst) countPairListPair
  endCounts =  bimapBoth (fmap snd) countPairListPair
  startConfig = combineIntoConfig phase startCounts startSig
  (endPh, endTape) = configToET $ combineIntoConfig phase endCounts endSig
  ans = Skip startConfig (SkipStepped endPh (Middle endTape)) Empty
  msg = "guessed " <> showP ans
  in
  --force $
  --trace msg $
  assertMsg (isSameInAsOut ans) msg ans

combineIntoConfig :: (Show s) => Phase -> ([Count], [Count]) -> Signature s -> Config Count s
combineIntoConfig phase (leftCounts, rightCounts) sig@(Signature leftBits p rightBits) =
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
    --trace ("zipping:\n" <> show (show sig <> "\n" <> pretty pair) <> "\nzipped\n")
    ans

--gets the simulation history and the displacement history
--normally these are output backwards which is of course crazy so we fix them here  
simForStepNumFromConfig :: (Partial, TapeSymbol s) => Int -> Turing -> Config Count s -> (TapeHist s Count, ReadShiftHist)
simForStepNumFromConfig limit machine startConfig
    = (second deInfCount $ finalState ^. s_history, finalState ^. s_readshift_history)
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

generalizeHistories :: forall s. (TapeSymbol s, Partial)
  => NonEmpty (Natural, [(Phase, ExpTape s InfCount)], [ReadShift])
  -> Either Text (Skip Count s)
generalizeHistories simWithNums = --trace ("sims were: " <> showP sims) 
  res where
  --simNums :: NonEmpty Natural
  simNums = view _1 <$> simWithNums
  sims = assertMsg (length simWithNums > 1) ("sims too short") (\(_x, y, z) -> (y, z)) <$> simWithNums
  startPhases = flip (^?!) (_1 . ix 0 . _1) <$> sims
  startPhase = guardMsg (list1AllEqual startPhases) "start phases not equal" $> head startPhases
  finalPhases = flip (^?!) (_1 . _last . _1) <$> sims
  finalPhase = guardMsg (list1AllEqual finalPhases) "end phases not equal" $> head finalPhases
  --the problem is these slicedpairs may not all have the same signature as the original thing 
  --which we are trying to generalize

  --generalizes against the numsToSimulateAt from above 

  --the outer Either is in case we fail. the inner maybe is because sometimes we don't generalize against the simnum at all, 
  --in which case the simnum is irrelevant 
  generalizeCL :: Partial => NonEmpty Count -> Either Text (Maybe Count, Count)
  generalizeCL cl = if list1AllEqual cl
      then Right (Nothing, head cl)
      --the problem with discarding the fst element of this pair, is that if you generalize (3,1) (4,2), then the first
      --the pair is (x + 2, x), but by discarding the first element, you're implcitly assuming it's x, more-or-less, so 
      --that ends up not working 
      else let
        ans = first pure <$> generalizeFromCounts (neZipExact (FinCount <$> simNums) cl)
        msg = "generalized:" <> show (pretty cl) <> "\ngot\n" <> show (pretty ans)
      in
        -- trace msg 
        ans
  {-algorithm:
  first, generalize all the counts to pairs, with the simnum we put in. you 
  might think we're done now, and we just want the second number of this pair. 
  I also thought this, but that is not correct, because in the two pairs 
  (x, x) (x + 2, x), that second x does not mean the same thing!
  therefore, the second thing to do is to make a big list of all the first 
  elements of the pairs, and calculate their "maximum" (smallest thing you 
  can add something to all of them to get). Third, map across all the pairs 
  again, adding to both elements whatever it takes to get the first element 
  to the maximum, and then discarding the first element, to leave just the 
  second element. 
  -}
  bigTraverse = bitraverseBoth . bitraverseBoth . traverse
  res = do
      let slicedPairs :: NonEmpty (ExpTape s Count, ExpTape s Count)
          slicedPairs = let
            ans = (\(hist, rSs) -> --trace ("hist: " <> showP hist) $
               if length hist <= 1 then error "<=1 length hist" else
                    getReadShiftSlicePair hist rSs 0 (length hist - 1)) <$>
              sims
            msg = "slicedPairs were:\n" <> show (pretty ans)
            in
            --trace msg 
              ans
          startSignatures = tapeSignature . fst <$> slicedPairs
          endSignatures = tapeSignature . snd <$> slicedPairs
      --after you slice them, they may no longer all be the same signature
      --for now, lets just assume they are
      guardMsg (list1AllEqual startSignatures && list1AllEqual endSignatures) "all sigs not equal"
      let
          countLists :: NonEmpty (([Count], [Count]), ([Count], [Count]))
          countLists = --trace ("slicedpairs" <> showP slicedPairs) 
            fmap (bimapBoth getCounts) slicedPairs
          flippedCountLists = --trace ("countlists " <> showP countLists) 
            transposeOverTwoPairs countLists
      countPairLists <- --trace ("flipcountls" <> showP flippedCountLists) 
        bigTraverse generalizeCL flippedCountLists
      let listOfFirstElements = (bifoldMapBoth . bifoldMapBoth . foldMap)
            (maybeToList . fst) countPairLists
          --todo does this do the right thing
          maxFirstElt = case listOfFirstElements of
            [] -> error "empty list of first elements"
            (x : xs) -> maximum listOfFirstElements
      ((s_cls, s_crs), (e_cls, e_crs)) <-
        bigTraverse (resolveCountPair maxFirstElt) countPairLists
      s_ph <- --trace ("cpls: " <> showP countPairLists) 
        startPhase
      e_ph <- finalPhase
      let startSig = head startSignatures
          endSig = head endSignatures
          guessedStartConfig = etToConfig s_ph $ zipSigToET startSig (s_cls, s_crs)
          skipOut = Skip
            guessedStartConfig
            (SkipStepped e_ph $ Middle $ zipSigToET endSig (e_cls, e_crs))
            (FinCount 100)  --TODO
          msg = "guessedWhatsNext " <> showP skipOut
      --force $ trace msg $ 
      assert (isSameInAsOut skipOut) $
        pure skipOut



{-takes in a machine, a tape configuration, and a symbolvar present in that tape configuration 
to generalize over. attempts to generate a skip with that config as a starting point
algorithm: instatiate the variable at several values, simulate forward a bunch of steps
take all signatures that occurred in each simulation, and try to generalize accross them, 
starting with the simplest first (eg, if 010 occurred many times, try to guess the function that
generates the coefficients of 0 1 and 0 from the instantiated symbolvar) 

right now generalizeFromCounts returns always (BoundVar 0), so as a hack we're going to change 
the symbolvar in the input config to be (BoundVar 0) also so it is the same

a lot of the possible "guesswhathappensnext"s are true but are once again not proveable via weak 
induction, so we're going to return a list of them instead, in the hopes that one works
for now, lets do all of the ones that have the same signature complexity as the minimum
-}
guessWhatHappensNext :: forall s. (TapeSymbol s)
  => Turing -> Config Count s -> SymbolVar -> [Skip Count s]
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
    simsAtNums :: NonEmpty ([(Phase, ExpTape s Count)], [ReadShift])
    simsAtNums = let
      ans = bimap getTapeHist getReadShiftHist <$> ((\(x,y) -> simForStepNumFromConfig x machine
        $ replaceSymbolVarInConfig True startConfig varToGeneralize
        $ FinCount y) <$> pairsToSimulateAt)
      -- msg = toString $ T.intercalate "startsim:\n" $ (\x -> "length: " <> show (length x) <> "\n" <> displayHist x) .
      --   fmap (fmap (second NotInfinity)) . fst <$> toList ans
      in
      --trace msg 
      ans
    --occurred in all simulations 
    sigsWhichOccurred :: Set (Phase, Signature s)
    sigsWhichOccurred = let
        (sig1 :| restSignatures) = fromList . fmap (fmap tapeSignature) . view _1 <$> simsAtNums
        ans = foldr S.intersection sig1 restSignatures
        msg = "allSigs occurred were:" <> toString (T.intercalate "\n" $ show <$> toList ans) <> "end allsigsoccured\n"
      in --force 
        -- $ trace msg 
        ans
    --generalizes an ending signature if possible
    generalizeOneSig :: (Phase, Signature s) -> Maybe (Skip Count s)
    generalizeOneSig pSig = rightToMaybe $ generalizeHistories simPairs
      where
        munge :: [(Phase, ExpTape s Count)] -> (Int, (Phase, ExpTape s Count))
        munge hist = case findIndex (\(p, t) -> (p, tapeSignature t) == pSig) hist of
            Nothing -> error "there was nothing with a signature we checked is in everything"
            Just i -> (i, hist !! i)
        --for each hisory, the time at which the signature occured, and the simstate at that point
        finalIndexAndConfig :: NonEmpty (Int, (Phase, ExpTape s Count))
        finalIndexAndConfig = let
             ans = munge . view _1 <$>  simsAtNums
             msg = "final indices and configs\n" <> toString (T.intercalate "\n" $ toList $ show . pretty <$> ans)
            in
          -- trace msg 
                ans
        finalIndices = view _1 <$> finalIndexAndConfig
        munge2 ::  NonEmpty (Natural, [(Phase, ExpTape s Count)], [ReadShift]) ->  NonEmpty (Natural, [(Phase, ExpTape s InfCount)], [ReadShift])
        munge2 = (fmap . second3 . fmap . fmap . second) NotInfinity
        simPairs :: NonEmpty (Natural, [(Phase, ExpTape s InfCount)], [ReadShift])
        simPairs = munge2 $ fmap (\(x, (y, z)) -> (x, y, z)) $ neZipExact numsToSimulateAt $
          (\(i, (th, rsh)) -> (takeExact (i+1) th, takeExact i rsh))
          <$> neZipExact finalIndices simsAtNums

{- We're trying to get the first element of the pair to be target, which will require modifying 
the second element, which we then return. if the first element is Nothing, it can be whatever and
thus we can just return the second element. 
To make the first element be equal to the target, we're going to try to substitute one variable 
in the first element to be equal to some of the second variable 
-}
resolveCountPair :: Count -> (Maybe Count, Count) -> Either Text Count
resolveCountPair target = \case
  (Nothing, s) -> Right s
  (Just f@(OneVar n as k x), s) -> do
    let (Count m bs ys) = target --we're casing down here so we're lazy in target
        (_likes, _rL, remRight) = likeTerms (ZeroVar n as) (ZeroVar m bs)
    countToMapTo <- failMsg "failed divide" $ (remRight <> Count 0 Empty ys) `divCount` k
    let updateMap = one (x, countToMapTo)
        updatedF = updateCount updateMap f
        updatedS = updateCount updateMap s
        msg = "updated " <> showP (f, s)
          <> " to match " <> showP target
          <> " getting " <> showP (updatedF, updatedS)
    --trace msg $
    assert (updatedF == target) $ pure updatedS
  (Just f, s) -> if f == target then Right s else error ("failed to resolve: " <> showP (target, f, s))

--skipContainsVar :: Skip Count Bit -> Bool
thingContainsVar :: (Bifoldable p) => p Count b -> Bool
thingContainsVar = getAny . bifoldMap (Any . countContainsVar) (const mempty) where
    countContainsVar = \case
        FinCount _n -> False
        _notFin -> True

getBoundVars :: (Bifoldable p) => p Count b -> [BoundVar]
getBoundVars = bifoldMap getCountBVs (const mempty) where
  getCountBVs (Count _n _as xs) = keys xs

guessAndProveWhatHappensNext :: (TapeSymbol s) => Turing -> SkipBook s -> Config Count s
  -> SymbolVar -> [(Skip Count s, SkipOrigin s)]
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
generalizeFromCounts :: NonEmpty (Count, Count) -> Either Text (Count, Count)
generalizeFromCounts xs = let
 ans = case  allEqualPair <|> additivePair <|> affinePair of
  Just x -> Right x
  Nothing -> Left $ "failed to generalize the pairs: " <> showP xs
  in
  --trace ("generalized " <> showP xs <> "\nto: " <> showP ans )
    ans
  where
    allEqualPair :: Maybe (Count, Count)
    allEqualPair = guard (list1AllEqual xs) >> pure (head xs)
    -- allEqualPair = (head xs) `someIf` (list1AllEqual xs)
    countToMaybeNat = \case
        Count n Empty Empty -> Just n
        _ -> Nothing
    naturalPairs :: Maybe (NonEmpty (Natural, Natural))
    naturalPairs = let
        ans = traverse (bitraverseBoth countToMaybeNat) xs
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
        --trace msg 
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
    additivePair = let
      ans = differences >>= \case
        ds@(d1 :| _rest) -> guard (list1AllEqual ds) >> pure (generalizeAddDiff d1)
      in
      --trace ("add diff: " <> showP ans)
      ans
    --isYmxplusb
    conformsToAffine :: Natural -> Int -> (Natural, Natural) -> Bool
    conformsToAffine m b (x, y) = fromIntegral x * fromIntegral m + b == fromIntegral y
    generalizeMulDiff :: Natural -> Int -> (Count, Count)
    generalizeMulDiff m b = let
      ans = if b >= 0
        then (newBoundVarBad, m `nTimes` newBoundVarBad <> finiteCount (fromIntegral b))
        --this is the line we need to change
        --note: x -> 2x - 1 is not the same as x + 1 -> 2x !!
        --so given 2x - 1 we compute the smallest multiple of 2 bigger than or equal to 1 (1), 
        --called toMul and then x + toMul is like subtracting 2 * toMul, so we have to add 
        --that back on the other side, except for the b we are actually supposed to subtract
        else let
          toMul = fromIntegral (-b) `ceilDiv` m
          --do subtraction in int space and then go back to natural space
          c = fromIntegral (fromIntegral (toMul * m) + b)
          in
          (newBoundVarBad <> finiteCount toMul, m `nTimes` newBoundVarBad <> finiteCount c)
      in
      --trace ("mul diff: " <> showP ans)
      ans
    affinePair :: Maybe (Count, Count)
    affinePair = do
      nps <- naturalPairs
      guard (length nps >= 3)
      case nps of
        (_pair :| []) -> Nothing
        --going for x -> m * x + b - we assume m > 0 but b can be any integer
        -- does not handle x -> m * (x + a) + b - but probably could somehow?
        pairs@((x1, y1) :| (x2, y2) : _rest) -> do
            -- necessary, else m = 0 which is not allowed
            guard (y1 /= y2)
          --the idea here is we're going to subtract x1 from x2, and then divide by it, so it has to be strictly positive
          --while we're going to subtract y1 from y2 but not divide by it so it just has to be at least 0
          --note: this function can't handle division, but it could be upgraded to
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
    notInfinityCountPair = Right <$> (maybeAllCounts >>= (rightToMaybe . generalizeFromCounts))
    infCountToMaybeCount :: InfCount -> Maybe Count
    infCountToMaybeCount = \case
        Infinity -> Nothing
        NotInfinity c -> Just c
    maybeAllCounts :: Maybe (NonEmpty (Count, Count))
    maybeAllCounts = traverse (bitraverseBoth infCountToMaybeCount) xs
    packageResult :: Either () (Count, Count) -> (InfCount, InfCount)
    packageResult (Left ()) = (Infinity, Infinity)
    packageResult (Right tup) = bimapBoth NotInfinity tup



module Induction where

import Relude
import Control.Lens
import Data.Map.Monoidal (assocs)

import Util
import Count
import Skip
import ExpTape
import Turing
import SimulateSkip
import Data.Bits (Bits(bit))

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
    -- TODO :: we need to somehow figure out how to notice if we step off the edge
    -- of the input, because unlike that normally being zeros, that is not ok here
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

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

--goal: make a thing that takes a skip that might apply to a certain machine, 
--attempts to simulate forward to prove that skip using induction
-- the first int is the limit on the number of steps to take before giving up 
--the (skip bit) input is the goal to be proven, 
-- the BoundVar is the variable on which we are going to do induction
--returns Left with an error message 
--or Right with success
proveInductively :: Int -> Turing -> SimState -> Skip Bit -> BoundVar -> Either Text (SkipOrigin Bit)
proveInductively limit t state goal indVar = baseCase >> indCase where
    baseCase :: Either Text ()
    baseCase = undefined
    baseGoal :: Skip Bit
    baseGoal = replaceVarInSkip goal indVar $ finiteCount 1
    indCase :: Either Text (SkipOrigin Bit)
    indCase = undefined
    indGoal :: Skip Bit
    indGoal = replaceVarInSkip goal indVar $ symbolVarCount newSymbolVar 1
    newSymbolVar :: SymbolVar
    newSymbolVar = undefined

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
proveBySimulating :: Int -> Turing -> SimState -> Skip Bit -> Either Text Count
proveBySimulating limit t (SimState _ _ book _ _) (Skip start goal _ _) 
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
      | indMatch p tape goal = pure curCount
      | numSteps > limit = Left "exceeded limit while simulating"
      | otherwise = case skipStep t book p tape of
            Unknown e -> Left $ "hit unknown edge" <> show e
            Stopped _ _ _ -> Left "halted while simulating"
            Stepped Infinity _ _ _ -> Left "hopped to infinity"
            Stepped (NotInfinity hopsTaken) newPhase newTape _ 
                -> loop (numSteps + 1) newPhase newTape (curCount <> hopsTaken)
    indMatch :: Phase -> ExpTape Bit InfCount -> SkipEnd Bit -> Bool 
    indMatch p et se = case bitraverse pure deInfCount et of 
        Nothing -> False 
        Just (ExpTape ls point rs) -> case se of 
            EndSide ph dir xs -> (p == ph) && case dir of
                L -> xs == ls 
                R -> xs == rs 
            EndMiddle (Config ph c_ls c_p c_rs) 
                -> (p == ph) && (ls == c_ls) && (point == c_p) && (rs == c_rs)
      where 
        deInfCount Infinity = Nothing 
        deInfCount (NotInfinity c) = Just c 

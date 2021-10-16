module Main where

import Relude

import Control.Lens
import Data.Text as T (length)
import Data.Text.Read
import System.IO (hSetBuffering, stdout, BufferMode(..))

import Turing
import TuringExamples
import Count hiding (num)
import Skip
import Tape (dispTape)
import ExpTape
import Results
import Simulate
import SimulateSkip
import Display
import SimulationLoops (simulateManyBasicLoop)

-- num = finiteCount
--
-- varSkip :: Skip Bit
-- varSkip = Skip
--   (Config (Phase 0) [] (True, finiteCount 2, R) [(False, newBoundVar 0), (True, finiteCount 1)])
--   (Config (Phase 1) [(True, newBoundVar 0)] (False, newBoundVar 0, R) [] )
--
-- varTape :: ExpTape Bit Count
-- varTape = ExpTape
--   ([(True, num 3)])
--   (True, num 2, R)
--   ([(False, num 8), (True, num 2)])
--
-- varResult :: ExpTape Bit Count
-- varResult = ExpTape
--   ([(True, num 11)])
--   (False, num 8, R)
--   ([(True, num 1)])

bb2 :: Turing
bb2 = Turing {states = 2, transitions = fromList
  [((Phase 0, False), Step (Phase 1) True L)
  ,((Phase 0, True), Step (Phase 1) True R)
  ,((Phase 1, False), Step (Phase 0) True R)
  ,((Phase 1, True), Halt)
  ]}

loop2 :: Turing
loop2 = Turing {states = 2, transitions = fromList
  --should step left and right forever
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) False R)
  --these two don't matter
  ,((Phase {unPhase = 0},True),Halt) --Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 1},True),Halt)
  ]}

--
jumps_to_end :: Turing
jumps_to_end = Turing {states = 2, transitions = fromList
  [((Phase 0,False),Step (Phase 1) True  R)
  ,((Phase 1,False),Step (Phase 1) False R)
  ]}

--this halted after a bit more time to simulate the OffToInfinityN proof
not_halt3 :: Turing
not_halt3 = Turing {states = 3, transitions = fromList [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L),((Phase {unPhase = 0},True),Halt),((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) True R),((Phase {unPhase = 1},True),Step (Phase {unPhase = 2}) False L),((Phase {unPhase = 2},False),Step (Phase {unPhase = 1}) True R),((Phase {unPhase = 2},True),Step (Phase {unPhase = 0}) True L)]}

false_backward_search :: Turing
false_backward_search = Turing {states = 3, transitions = fromList
  [((Phase 0, False), Step (Phase 1) True R)
  -- ,((Phase 0, True ), Halt)
  ,((Phase 1, False), Step (Phase 2) False R)
  -- ,((Phase 1, True ), Step (Phase 1) True  R)
  -- ,((Phase 2, False), Step (Phase 2) True  L)
  -- ,((Phase 2, True ), Step (Phase 0) True  L)
  ]}

-- the most ones was Just 6, performed by
-- 0 False | 1 True R
-- 0 True | Halt
-- 1 False | 2 False R
-- 1 True | 1 True R
-- 2 False | 2 True L
-- 2 True | 0 True L
-- final tape:Just "1>1<1 1 1 1"


--the most ones was Just 5
-- 0 False | 1 True R
-- 0 True | Halt
-- 1 False | 1 True L
-- 1 True | 2 False L
-- 2 False | 0 True R
-- 2 True | 2 True R

simProgram :: (a -> Text) -> Results a -> IO ()
simProgram display results = do
  hSetBuffering stdout NoBuffering
  putTextLn $ dispResults display $ results
  interact results where
  interact r = do
    putText "Would you like to run a machine listed above?\n If so, enter it's index, else hit enter to exit:"
    maybeIndex <- getLine
    case decimal maybeIndex of
      Left _ -> return ()
      Right (i::Int, _) -> case r ^? unprovenExamples . ix i . _1 of
        Nothing -> do
          putTextLn "indexNotFound"
          interact r
        Just machine -> showMachine r where
          showMachine r = do
            putText "How many steps? Prompt:"
            steps <- getLine
            case decimal steps of
              Left _ -> showMachine r
              Right (steps::Int, _) -> do
                putTextLn $ "simulating machine: " <> show i <> "\n" <> show machine
                putTextLn $ showOneMachine machine steps
                interact r


--TODO:: test skip gluing logic
--TODO:: write skip-proves-infinity logic
--TODO:: fix end-of-tape detection issue --seraphina two months later doesn't remember what this is
--TODO:: make simple induction
--TODO:: make macro machine simulator
--TODO:: make database that stores results of machines, so that results can be compared between different runs

--above todos are old 
--planet — Today at 9:52 PM (3 Oct 2021)
--next Todos: 
--see if it can actually prove said inductions 
--add in logic to detect when an induction means a machine will run forever
--add in cycle checking
--that will leave the only size 3 machine that is unproven the checkerboard sweeper, I think
--
--next todos, rewritten: 
-- figure out how to make induction guesser guess things of the right length in/out
-- attempt to connect induction guesser to induction prover
-- when we prove new skips, add logic to detect when that skip proves a machine will run forever
-- -- make the simulateMultipleMachinesOuterLoop function
-- -- using the history feature, check if we ever cycle and use that as a proof of nonhalting 
-- 
-- add the monad that is used to generate fresh bound and symbol variables 
-- check the backwards search code works ok 
-- add backwards search to skip-based sim
-- add end-of-tape heuristic to skip-based sim (I think maybe glueing actually just accomplishes this)
--
-- more todos
-- add deflection to left and right tracking (added to skips, now just need to add to simstate / applyskip)
-- use deflection tracking to do the end of tape cycle guesser right
-- use deflection tracking to do the better induction guesser 
main :: IO ()
main = do
  -- let results = Simulate.simulate 140 $ startMachine1 3
  -- simProgram dispTape results
  
  let resultList :: [(Turing, SimResult (ExpTape Bit InfCount))] =  simulateManyBasicLoop 100 $ startMachine1 3 
  putText $ dispResults dispExpTape $ foldr (uncurry addResult) Empty resultList 

  -- let skipResults = simulateWithSkips 1000 $ startMachine1 5
  -- simProgram dispExpTape skipResults

  -- putTextLn $ showOneMachine bb2 10
  -- putTextLn $ displaySkipSimulation jumps_to_end 2
 
  -- print $ backwardSearch $ startMachine1 3 --this returns a proof which is bad
  -- print $ backwardSearch $ false_backward_search
  -- traverse_ putTextLn $ show <$> backwardSearch <$> tnfPrecursors 25 bb3
  -- traverse_ putTextLn $ dispTuring <$> tnfPrecursors 25 bb3
  --putTextLn $ showOneMachine bb3 100
  -- putStrLn $ force $ simpleSimulator 2 20

-- num states and num machines
-- 3 4,052
-- 4 618,296
-- 5 126,382,022

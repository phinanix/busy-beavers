module Main where

import Relude

import Control.Lens
import Data.Text as T (length)
import Data.Text.Read
import System.IO (hSetBuffering, stdout, BufferMode(..))

import Turing
import Count
import Skip
import ExpTape
import Simulate
import Display

bb2 :: Turing
bb2 = Turing {states = 2, transitions = fromList
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) True L)
  ,((Phase {unPhase = 0},True),Step (Phase {unPhase = 1}) True R)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 1},True),Halt)
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

--this halted after a bit more time to simulate the OffToInfinityN proof
not_halt3 :: Turing
not_halt3 = Turing {states = 3, transitions = fromList [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L),((Phase {unPhase = 0},True),Halt),((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) True R),((Phase {unPhase = 1},True),Step (Phase {unPhase = 2}) False L),((Phase {unPhase = 2},False),Step (Phase {unPhase = 1}) True R),((Phase {unPhase = 2},True),Step (Phase {unPhase = 0}) True L)]}

--woah, this is a counting machine !!!
weird3 :: Turing
weird3 = Turing {states = 3, transitions = fromList
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L)
  ,((Phase {unPhase = 0},True) ,Step (Phase {unPhase = 0}) False R)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 2}) True L)
  ,((Phase {unPhase = 1},True ),Halt)
  ,((Phase {unPhase = 2},False),Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 2},True ),Step (Phase {unPhase = 2}) True L)
  ]}

almostweird3 :: Turing
almostweird3 = Turing {states = 3, transitions = fromList
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 2}) False L)
  ,((Phase {unPhase = 0},True) ,Step (Phase {unPhase = 0}) False R)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 2}) True L)
  ,((Phase {unPhase = 1},True ),Halt)
  ,((Phase {unPhase = 2},False),Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 2},True ),Step (Phase {unPhase = 2}) True L)
  ]}

fullsim_not_halt3 :: Turing
fullsim_not_halt3 = Turing {states = 3, transitions = fromList
  [((Phase 0,False),Step (Phase 1) True  R)
  ,((Phase 0,True ),Step (Phase 2) False R)
  ,((Phase 1,False),Step (Phase 2) False L)
  ,((Phase 1,True ),Step (Phase 0) True  L)
  ,((Phase 2,True ),Step (Phase 0) True  L)
  ]}

--0 False | 1 True R\n0 True | Halt\n1 False | 1 True L\n1 True | 2 False L\n2 False | 0 True R\n2 True | 2 True R\n
bb3 :: Turing
bb3 = Turing {states = 3, transitions = fromList
  [((Phase 0, False), Step (Phase 1) True R)
  ,((Phase 0, True ), Halt)
  ,((Phase 1, False), Step (Phase 2) False R)
  ,((Phase 1, True ), Step (Phase 1) True  R)
  ,((Phase 2, False), Step (Phase 2) True  L)
  ,((Phase 2, True ), Step (Phase 0) True  L)
  ]}

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

simProgram :: IO ()
simProgram = do
  hSetBuffering stdout NoBuffering
  let results = Simulate.simulate 310 $ startMachine1 4
  putTextLn $ dispResults $ results
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
            putText $ "How many steps? Prompt:"
            steps <- getLine
            case decimal steps of
              Left _ -> showMachine r
              Right (steps::Int, _) -> do
                putTextLn $ "simulating machine: " <> show i
                putTextLn $ showOneMachine machine steps
                interact r

--
exampleSkip :: Skip Bit
exampleSkip = Skip
  (Config (Phase 0) [] (False, finiteCount 2, R) [(False, finiteCount 2), (True, finiteCount 1)])
  (Config (Phase 1) [(True, finiteCount 3)] (False, finiteCount 4, L) [(True, finiteCount 5)])

exampleExpTape :: ExpTape Bit Count
exampleExpTape = ExpTape
  ([(True, finiteCount 1), (False, finiteCount 3), (True, finiteCount 1)])
  (False, finiteCount 10, R)
  ([(False, finiteCount 2), (True, finiteCount 3), (False, varCount 0)])

--
exampleSimpleSkip :: Skip Bit
exampleSimpleSkip = Skip
  (Config (Phase 0) [] (False, finiteCount 2, R) [])
  (Config (Phase 1) [(True, finiteCount 3)] (False, finiteCount 4, L) [(True, finiteCount 5)])

exampleExpTape2 :: ExpTape Bit Count
exampleExpTape2 = ExpTape
  ([(True, finiteCount 1), (False, finiteCount 3), (True, finiteCount 1)])
  (False, finiteCount 10, R)
  ([(False, finiteCount 2), (True, finiteCount 3), (False, varCount 0)])

--TODO:: make exponential notation for tape
--TODO:: make simple induction
--TODO:: make macro machine simulator
--TODO:: make database that stores results of machines, so that results can be compared between different runs
main :: IO ()
main = do
  --simProgram
  let result = applySkip exampleSimpleSkip ((Phase 0), exampleExpTape)
  putTextLn $ fromMaybe "fail" $ dispSkipResult <$> result
  -- print $ backwardSearch $ startMachine1 3 --this returns a proof which is bad
  -- print $ backwardSearch $ false_backward_search
  -- traverse_ putTextLn $ show <$> backwardSearch <$> tnfPrecursors 25 bb3
  -- traverse_ putTextLn $ dispTuring <$> tnfPrecursors 25 bb3
  --putTextLn $ showOneMachine bb3 100
  -- putStrLn $ force $ simpleSimulator 2 20

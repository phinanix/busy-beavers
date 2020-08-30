module Main where

import Relude

import Control.Lens
import Data.Text as T (length)
import Data.Text.Read
import System.IO (hSetBuffering, stdout, BufferMode(..))

import Beaver
import SimulateSimple
import Simulate
import DisplaySimple
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

simProgram :: IO ()
simProgram = do
  hSetBuffering stdout NoBuffering
  let results = Simulate.simulate 20 $ startMachine1 3
  putStrLn $ dispResults $ results
  interact results where
  interact r = do
    putText "Would you like to run a machine listed above?\n If so, enter it's index, else hit enter to exit:"
    maybeIndex <- getLine
    case decimal maybeIndex of
      Left _ -> return ()
      Right (i::Int, _) -> case r ^? unprovenExamples . ix i . _1 of
        Nothing -> do
          putStrLn "indexNotFound"
          interact r
        Just machine -> showMachine r where
          showMachine r = do
            putText $ "How many steps? Prompt:"
            steps <- getLine
            case decimal steps of
              Left _ -> showMachine r
              Right (steps::Int, _) -> do
                putTextLn $ "simulating machine: " <> show i
                putStrLn $ showOneMachine machine steps
                interact r

--TODO:: make exponential notation for tape
--TODO:: make simple induction
--TODO:: make macro machine simulator
main :: IO ()
main = simProgram
  --
  --putStrLn $ showOneMachine fullsim_not_halt3 100
  -- putStrLn $ force $ simpleSimulator 2 20

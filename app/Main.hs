module Main where

import Relude

import Control.Lens
import qualified Data.Text as T (length)
import Data.Text.Read
import Prettyprinter
import Control.Monad
import qualified Data.Vector as V

import Turing
import TuringExamples
import Notation
import Count hiding (num)
import Skip
import Tape (dispTape)
import ExpTape
import Results
import Simulate
import SimulateSkip
import Display
import SimulationLoops (simulateManyBasicLoop)
import MoreSimulationLoops
import Util
import OuterLoop
import System.IO (openFile, hGetContents, hClose)


simProgram :: (Pretty s, Pretty c, Show s, Show c) => Results c s  -> IO ()
simProgram results = do
  hSetBuffering stdout NoBuffering
  putTextLn $ dispResults results
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
-- -- figure out how to make induction guesser guess things of the right length in/out
-- attempt to connect induction guesser to induction prover
-- when we prove new skips, add logic to detect when that skip proves a machine will run forever
-- -- make the simulateMultipleMachinesOuterLoop function
-- -- using the history feature, check if we ever cycle and use that as a proof of nonhalting 
-- 
-- add the monad that is used to generate fresh bound and symbol variables 
-- check the backwards search code works ok 
-- add backwards search to skip-based sim
-- -- add end-of-tape heuristic to skip-based sim (I think maybe glueing actually just accomplishes this)
--
-- more todos
-- -- add deflection to left and right tracking (added to skips, now just need to add to simstate / applyskip)
-- -- use deflection tracking to do the end of tape cycle guesser right
-- -- use deflection tracking to do the better induction guesser 

-- more todos 27 nov 
-- fix step and displacement tracking in induction guesser / prover
-- select between different successful inductions via total number of steps?
-- split bw search into DFS and graph-gen so it can be better tested
-- make induction guesser use the "guesswhathappensnext" feature to get unstuck
-- make induction guesser "finish the proof" once it is unstuck, 
--       so it can prove inductions with the same sig in and out
-- integrate induction guesser into overall simulation loop; tune it 

readFile :: String -> IO String
readFile filename = do
        handle <- openFile filename ReadMode
        contents <- hGetContents handle
        hClose handle
        pure contents

main :: IO ()
main = do
  -- let results = Simulate.simulate 100 $ startMachine1 4
  -- simProgram dispTape results

  --let resultList
  --       :: [(Turing, SimResult (ExpTape Bit InfCount))] 
  --       = indProveLoopMany 141 $ startMachine1 4
  -- let resultList 
  --       :: [(Turing, SimResult InfCount   Bit)]
  --       = bestCurrentProveLoop 141 $ startMachine1 3
  --simProgram dispExpTape $ foldr (uncurry addResult) Empty resultList 
  --putTextLn $ dispResults $ foldr (uncurry addResult) Empty resultList 
  --let continues = getContinues $ outerLoop basicTacticVector (startMachine1 4)
  fileContents <- Relude.readFile "size4_unfinished_16_jul.txt"
  let machineStrings = lines $ fromString fileContents
      machines = unm <$> machineStrings
      enumMachines = zip [0,1 ..] machines
      runTactic = getContinues . outerLoop m3456TacticVector
      runTacticPrint (i, m) = trace ("machine: " <> show i) runTactic m
      unprovenMachines = bind runTacticPrint enumMachines


  putText $ "there were: " <> show (length unprovenMachines) <> " machines unproven:\n"
  traverse_ (putText . (\m -> machineToNotation m <> "\n")) unprovenMachines

  --putText $ "there were: " <> show (length continues) <> " machines unproven:"
  --traverse_ putPretty continues

  -- let assertFails = checkLRAssertManyMachines 200 $ startMachine1 4
  -- for_ assertFails putTextLn 

-- crash on
-- TR1FL2FL0FR1TR0TR3TL0___


-- num states and num machines
-- 3 4,052
-- 4 618,296
-- 5 126,382,022

--size 3
--indprove 0.73s 
--bestcurprove 1.27s  
--both leave 31 

--size 4
--indprove 3m23s leaving 6650
--bestcurprove 4m01s leaving 4729
--bestcurprove became 17m34s after making a shit ton of stuff general
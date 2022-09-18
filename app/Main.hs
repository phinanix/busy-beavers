module Main where

import Relude

import Control.Lens
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Text.Read
import Prettyprinter
import Control.Monad
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Map as M

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
import Scaffold

import System.IO (openFile, hGetContents, hClose)
import Control.Exception


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

loadMachinesFromFile :: String -> IO [Turing]
loadMachinesFromFile fn = do
  fileContents <- TIO.readFile fn
  pure $ unm <$> lines fileContents

applyTactic :: Vector Tactic -> [Turing] -> [(Int, Turing)]
applyTactic tac machines = let
    enumMachines = zip [0,1 ..] machines
    runTactic = getContinues . outerLoop tac
    runTacticPrint (i, m) = (i,) <$> trace (toString $ "machine: " <> show i <> "\n" 
      <> machineToNotation m) runTactic m
    unprovenMachines = bind runTacticPrint enumMachines
  in
    unprovenMachines

tacticVectors :: (Ord a, IsString a) => Map a (Vector Tactic)
tacticVectors = M.fromList
  [ ("backward", bwSearchTacticVector)
  , ("all", everythingVector)
  , ("basic", basicTacticVector)
  , ("constructive", constructiveVector)
  , ("noncon", nonconVector)
  ]

putMachinesInFile :: [Turing] -> String -> IO ()
putMachinesInFile ms fn = do
  let machineString = T.intercalate "\n" $ machineToNotation <$> ms
  TIO.writeFile fn machineString

processMachinesViaArgs :: IO ()
processMachinesViaArgs = do
  args <- getArgs
  let [tacticName, inputFile, outputFile] = assert (length args == 3) args
      tacticVec = tacticVectors ^?! ix tacticName 
  inputMachines <- loadMachinesFromFile inputFile 
  let inputMessage = "read " <> show (length inputMachines) 
       <> " machines as input. running: " <> fromString tacticName
       <> "\n"
  putText inputMessage
  let unprovenMachinesWNums = applyTactic tacticVec inputMachines 
      unprovenMachines = snd <$> unprovenMachinesWNums
  putMachinesInFile unprovenMachines outputFile 
  putText inputMessage
  putText $ "finished with " <> show (length unprovenMachines) 
    <> " machines not proven, written to file\n"


main :: IO ()
main = do
    let x = numToLet 5
    putText (show x) 
    processMachinesViaArgs
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




  --putText $ "there were: " <> show (length continues) <> " machines unproven:"
  --traverse_ putPretty continues

  -- let assertFails = checkLRAssertManyMachines 200 $ startMachine1 4
  -- for_ assertFails putTextLn 

{-
30 jul todo
1) read tms from file
"readMachinesFromFile"
2) get cl args
"gatArgs"
3) execute a given tactic vector on machines
"applyTactic"
4) tactic vectors have names
"tacticVectors"
5) output tms to file
"putMachinesInFile"
6) print summary output stats (# input machines, # holdouts)
-}
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
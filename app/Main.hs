module Main where

import Relude
import qualified Relude.Unsafe as U

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
import Runner
import Data.Char
import Data.List (isSuffixOf)

--interactive program that lets you display machines that are not solved 
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
    runTacticPrint (i, m) = (i,) <$> 
      trace (toString $ "machine: " <> show i <> "\n" <> machineToNotation m) 
      runTactic m
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
  , ("abs", absVector)
  , ("fast", fastTacticVector)
  , ("splitter", splitterTacticVector)
  ]

putMachinesInFile :: [Turing] -> String -> IO ()
putMachinesInFile ms fn = do
  let machineString = T.intercalate "\n" $ machineToNotation <$> ms
  TIO.writeFile fn machineString

--interactive program which lets you read machines from a file, apply a named tactic, and write machiens
--to another file which are not solved
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

{-
CLI for runnerDotPy
experimentName
tacticName 
chunkSize 
inputMachines --todo 

inputMachines either ends with `.txt` in which case it is interpreted as a 
plain text list of machines, one per line
or does not, in which case it must be of the form seed_x_y where x is 0 or 1
and y is a single digit. x is the symbol that the machine writes on the 
first step, and y is the number of states to enumerate. 
-}

usageMessage :: Text 
usageMessage = "usage: stack exec busy-beavers-exe experimentName tacticName chunkSize inputMachines" 
  <> "\ninputMachines: either a .txt or seed_bit_stateCount\n" 

getMachines :: String -> IO [Turing] 
getMachines inputMachineString = if ".txt" `isSuffixOf` inputMachineString
  then loadMachinesFromFile inputMachineString
  else case inputMachineString of 
    ['s', 'e', 'e', 'd', '_', bit, '_', numStates] -> 
      let machineFunc = case bit of 
            '0' -> startMachine0 
            '1' -> startMachine1 
            _ -> invalidStr 
      in 
      pure [machineFunc (digitToInt numStates)]
    _ -> invalidStr 
    where 
    invalidStr :: a 
    invalidStr = error $ fromString $ inputMachineString <> " is not a valid machine string"

runnerDotPyFromArgs :: IO () 
runnerDotPyFromArgs = do 
  args <- getArgs 
  case args of 
    [experimentName, tacticName, chunkSizeString, inputMachineString] -> do 
        let chunkSize :: Int = U.read chunkSizeString
            tacticVec = tacticVectors ^?! ix tacticName 
        inputMachines <- getMachines inputMachineString
        let inputMessage = "recieved " <> show (length inputMachines) 
              <> " machines as input. running: " <> fromString tacticName
              <> "\n"
        putText inputMessage
        runnerDotPy tacticVec inputMachines (fromString experimentName) chunkSize
        putText inputMessage
        aggregateFiles experimentName

    _ -> putText usageMessage

main :: IO ()
main = do
  runnerDotPyFromArgs

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
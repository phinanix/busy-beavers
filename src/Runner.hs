module Runner where


import Relude
import Control.Lens hiding ((.=))
import qualified Relude.Unsafe as U
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Set as S
import qualified Data.List.NonEmpty as NE
import Relude.Extra (bimapBoth)
import Prettyprinter
import Safe.Exact
import Control.Exception (assert)
import Safe.Partial
import Data.Binary.Get

import Data.ByteString.Builder as BS
import Data.Bits
import qualified Data.ByteString.Lazy as BL
import Data.Vector.Fixed.Unboxed ( Vec )
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Text.Lazy.IO as TLIO
import qualified Data.Text.IO as TIO
import qualified Data.Ord

import Util hiding ((.:))
import Count
import Skip
import ExpTape
import Turing
import TapeSymbol
import HaltProof
import SimulateSkip
import Graphs
import Results
import Mystery
import Notation
import Data.Aeson
import Data.Text.Lazy.Builder (fromText, toLazyText)
import Data.Aeson.Text
import OuterLoop
import System.IO (withBinaryFile)
import System.Directory
import Data.List (isSuffixOf)
import System.FilePath
import Data.Text.Encoding (encodeUtf8Builder)
import Data.Typeable (typeOf, TypeRep, typeRep)
import Data.Aeson.Types (Parser)
import Data.Char (digitToInt)

{-
this file contains the code responsible for actually running all of the different 
deciders, enumerating all turing machines in a certain set, saving checkpoints to disk,
saving final results to disk, and so on. 
Desiderata: 
 - haltproofs are printed out in a nice text format
 - easy to from command line run a scan on a given size or resume a scan
 - every so often, all results so far are dumped to disk, plus a checkpoint that 
   can be used to resume the scan 
 - summary statistics that aggregate all results from a set of input files
 - maybe there is a typeclass for decider that includes its type of "extra data"
   and a function which gives a summary of what happened given machines and extra data
   eg for translated cyclers, it could give the machines which had the largest S and P 
 - maybe there is a file format that you feed to the runner that says things like 
   which deciders to run and in what order and stuff

output format: there are 4 files. 
1) a bitpacked file that stores all machines with results, where "result" is either 
   halting, translated cycle, other, or undecided, and there are 8 bytes of extra info 
   that depends on which result
   [machine (n bytes)][result 1][extra info 8 bytes]
   extra info for halting: 4 byte step count
   translated cycle: 2 byte period, 2 byte period-start-cap, 2 byte offset-per-period

2) a text file that stores all undecided machines 1 per line

3) a text file that stores all "other" machines from above, as JSON, to support a rich 
   text based decider output format

4) a checkpoint file, which is only output if the run isn't over, which contains all 
   machines currently on the tree-enumerate stack, 1 per line. running the program 
   with this file as input will resume the search from this point. 

the 3 output files can be freely concatenated together to create a single set of results
from a run. 

to bitpack a TM: 
you could turn each transition into 1 bit direction, 1 bit write, 3 bits state, which
is 5 bits / transition, which is 50 bits for size 5 = 7 bytes, and 60 bits for 
size 6 = 8 bytes. you can get size 5 down to 6 bytes by ommitting 2 bits, for example you 
could assume the first trans is ?RB which saves 4 bits. to save more bits, you 
could also encode the halting transition as 3 bits (which of the 8 transitions is it,
assuming it is neither the first nor the second transition) which puts you to 44 bits. 
that gives you 5 bits to use for the tag, which takes us from 8 bytes to 6 per 
machine+tag, but that seems overkill. 
bitpacked: 
130M 5 state machines * 16 bytes = 2GB.
"other":
3.5M 5 state machines * 200 bytes (30 for machine, 170 for decider) = 700MB
compression wise, the first one probably compresses less than 2x, while the second 
one probably compresses at least 10x and is the more interesting file anyway. 

todo: 
TM to bitpack 
TM+simresult to bitpack
generate bitpack file
simresult to json
generate json file
draft the overall loop
fill in more 
-}

bitSum :: (Foldable t, Num a) => t Bool -> a
bitSum = foldl' (\num bit -> 2*num + (if bit then 1 else 0)) 0

unBitSum :: Integral a => a -> Int -> [Bool]
unBitSum i n = snd $ iterate getOneBit (i, []) U.!! n where
  getOneBit (j, bs) = (j `div` 2, (j `mod` 2 == 1) : bs)

--most significant bit is head of list
packBits :: [Bool] -> Word64
packBits xs = assert (length xs <= 64) $ bitSum $ xs ++ replicate (64 - length xs) False

--a machine's transitions are encoded in the order: (0, F) (0, T) (1, F) and so on
encodeTM :: Turing -> Word64
encodeTM (Turing n transMap)
  = packBits $ foldMap (\e -> encodeTrans n $ transMap ^. at e ) $ uniEdge n

--a transition is 5 bits: [bit to write][direction][new state]
--bit to write is self explanatory
--direction is 0/1 to L/R
--new state is 0 to n-1 for normal transition, n for halt, n+1 for undefined 
encodeTrans :: Int -> Maybe Trans -> [Bool]
encodeTrans n = \case
  --undefined is 00 for bit and dir and n+1 for undefined 
  Nothing -> False : (False : intTo3Bit (n+1))
  --halt has TL which is 10 and n 
  Just Halt -> True : (False : intTo3Bit n)
  Just (Step (Phase p) (Bit b) d) -> b : ((d == R) : intTo3Bit p)

--most significant bit is head of list
intTo3Bit :: Int -> [Bool]
intTo3Bit i = assert ((i >= 0) && (i <= 7)) unBitSum i 3

unpackBits :: Word64 -> [Bool]
unpackBits w = unBitSum w 64

decodeTM :: Int -> Word64 -> Turing
decodeTM n w = let
  --foldl :: (b -> a -> b) -> b -> t a -> b 
  --b = ([Bool], [(Edge, Maybe Trans)]) 
  (rembits, etPairs) = foldl' (\(remBS, etOut) e ->
    let (nextTransBits, newRemBS) = splitAtExact 5 remBS in
      (newRemBS, (e, decodeTrans n nextTransBits) : etOut)
    )
    (unpackBits w, []) (uniEdge n)
  in assert (not $ or rembits) Turing n $ fromList $ mapMaybe (\(e, mt) -> (e,) <$> mt) etPairs

decodeTrans :: Int -> [Bool] -> Maybe Trans
decodeTrans n [b, d, x, y, z] = let ph = threeBitsToInt (x, y, z) in
  if ph == (n+1) then Nothing else if ph == n then Just Halt else
    Just $ Step (Phase ph) (Bit b) (if d then R else L)
decodeTrans n bs = error $ "decodeTrans: " <> show n <> " " <> show bs

threeBitsToInt :: (Bool, Bool, Bool) -> Int
threeBitsToInt (a,b,c) = bitSum [a,b,c]

packWord16Word64 :: (Word16, Word16, Word16, Word16) -> Word64
packWord16Word64 (w, x, y, z) = let [a,b,c,d] = fromIntegral <$> [w,x,y,z]
 in a `shiftL` 48 + b `shiftL` 32 + c `shiftL` 16 + d

unpackWord64Word16 :: Word64 -> (Word16, Word16, Word16, Word16)
unpackWord64Word16 inpWord = let [a,b,c,d] = extractBits <$> [48, 32, 16, 0] in
  (a,b,c,d) where
  extractBits :: Int -> Word16
  extractBits b = fromIntegral $ inpWord `shiftR` b

{-the Word8 is a tag with the following meanings. 
  the Word64 is extra data that each tag above can use for anything. 
0 -> halted. word64 is one number encoding number of steps to halt
1 -> translated cycler. word64 is 3 word16s encoding starts-by, period, offset, and a blank one. 
2 -> undecided. word64 is empty
3 -> decided infinite by other means. word64 is empty
_ -> reserved for later use

-}
bitEncodeSimResult :: Mystery TapeSymbol (SimResult InfCount) -> (Word8, Word64)
bitEncodeSimResult (Mystery res) = case res of
  Halted n _ft -> (0, fromIntegral n)
  ContinueForever (LinRecur s p t)
    -> packLR s p t
  ContinueForever (Cycle s p) -> packLR s p 0
  Continue {} -> (2, 0)
  ContinueForever _hp -> (3, 0)
  MachineStuckRes -> error "machine stuck bit encode"
  where
    packLR s p t = assertMsg
      (all (\x -> x >= 0 && x <= fromIntegral (maxBound :: Word16)) [s,p])
      ("bitpacker failed! s,p,t: " <> show (s,p,t))
      (1, packWord16Word64 (fromIntegral s, fromIntegral p, safeEncodeIntWord16 t, 0))

safeEncodeIntWord16 :: Partial => Int -> Word16
safeEncodeIntWord16 i = let
  max16Int :: Int = fromIntegral (maxBound :: Word16)
  half16 = (max16Int + 1) `div` 2
  negLim = (-half16) + 1
  cond = i >= negLim && i <= half16
  in assertMsg cond ("bitpacker, " <> show i <> " doesn't fit in two bytes")
    fromIntegral i

safeDecodeIntWord16 :: Word16 -> Int
safeDecodeIntWord16 w = let
  max16Int :: Int = fromIntegral (maxBound :: Word16)
  half16 = (max16Int + 1) `div` 2
  posAns :: Int = fromIntegral w
  in if posAns > half16 then posAns - (max16Int + 1) else posAns

data BitSimResult = BHalt Word64 | BLinRecur Word16 Word16 Word16
  | BContinue | BOtherInfinite deriving (Eq, Ord, Show, Generic)
instance NFData BitSimResult

bitDecodeSimResult :: Word8 -> Word64 -> BitSimResult
bitDecodeSimResult tag info = case tag of
  0 -> BHalt info
  1 -> let (s, p, t, z) = unpackWord64Word16 info in assert (z == 0) BLinRecur s p t
  2 -> BContinue
  3 -> BOtherInfinite
  _ -> error $ "bitdecodesimresult invalid tag: " <> show tag

packRes :: (Turing, Mystery TapeSymbol (SimResult InfCount)) -> Builder
packRes (t, res) = let (w8, w64) = bitEncodeSimResult res in
  word64BE (encodeTM t) <> word8 w8 <> word64BE w64

bitPackResults :: [(Turing, Mystery TapeSymbol (SimResult InfCount))] -> Builder
bitPackResults res = mconcat $ packRes <$> res

newtype SomeResult = SomeResult (Mystery TapeSymbol (SimResult InfCount))
  deriving (Eq, Ord, Show, Generic)

symbolTypeOfSomeResult :: forall c s. (TapeSymbol s)
  => SimResult c s -> TypeRep
symbolTypeOfSomeResult _res = typeRep (Proxy @s)

symbolRepToText :: TypeRep -> Text
symbolRepToText rep
  | rep == typeRep (Proxy @Bit) = "Bit"
  | rep == typeRep (Proxy @(Vec 2 Bit)) = "Vec 2 Bit"
  | rep == typeRep (Proxy @(Vec 3 Bit)) = "Vec 3 Bit"
  | rep == typeRep (Proxy @(Vec 4 Bit)) = "Vec 4 Bit"
  | rep == typeRep (Proxy @(Vec 5 Bit)) = "Vec 5 Bit"
  | rep == typeRep (Proxy @(Vec 6 Bit)) = "Vec 6 Bit"
  | rep == typeRep (Proxy @(Vec 7 Bit)) = "Vec 7 Bit"
  | otherwise = error $ "tried to print unknown rep:" <> show rep

textToParseFunc :: Text -> Value -> Parser (Mystery TapeSymbol (SimResult InfCount))
textToParseFunc typeName
  | typeName == "Bit" = fmap Mystery . parseJSON @(SimResult InfCount Bit)
  | typeName == "Vec 2" = fmap Mystery . parseJSON @(SimResult InfCount (Vec 2 Bit))
  | typeName == "Vec 3" = fmap Mystery . parseJSON @(SimResult InfCount (Vec 3 Bit))
  | typeName == "Vec 4" = fmap Mystery . parseJSON @(SimResult InfCount (Vec 4 Bit))
  | typeName == "Vec 5" = fmap Mystery . parseJSON @(SimResult InfCount (Vec 5 Bit))
  | typeName == "Vec 6" = fmap Mystery . parseJSON @(SimResult InfCount (Vec 6 Bit))
  | typeName == "Vec 7" = fmap Mystery . parseJSON @(SimResult InfCount (Vec 7 Bit))
  | otherwise = error $ "tried to parse unknown type: " <> show typeName

instance ToJSON SomeResult where
  toJSON :: SomeResult -> Value
  toJSON (SomeResult (Mystery res)) = object [
    "symty" .= symbolRepToText (symbolTypeOfSomeResult res),
    "result" .= toJSON res]

instance FromJSON SomeResult where
  parseJSON :: Value -> Parser SomeResult
  parseJSON = withObject "SomeResult" $ \v -> do
    tyName <- v .: "symty"
    let parseFunc = textToParseFunc tyName
    resJSON <- v .: "result"
    SomeResult <$> parseFunc resJSON


--a series of lines, each line is first a machine string and then a json blob 
--containing the simulation result
resultsToText :: [(Turing, Mystery TapeSymbol (SimResult InfCount))] -> _
resultsToText results = toLazyText $ foldMap mkLine $ filter (not . resIsBin . snd) results where
  mkLine :: (Turing, Mystery TapeSymbol (SimResult InfCount)) -> _
  mkLine (m, res)
    = fromText (machineToNotation m <> " ") <> encodeToTextBuilder (SomeResult res) <> fromText "\n"
  resIsBin :: Mystery TapeSymbol (SimResult InfCount) -> Bool
  resIsBin (Mystery res) = case res of
    Halted{} -> True
    Continue{} -> True
    ContinueForever hp -> case hp of
      LinRecur{} -> True
      Cycle{} -> True
      _ -> False
    MachineStuckRes -> error "machinestuck in resisbin"

machinesToText :: [Turing] -> Text
machinesToText = (<> "\n") . T.intercalate "\n" . fmap machineToNotation

{-
runner loop is overall quite similar to "outerLoop"
it takes tactics and a list of machines, and it outputs 
3 files: bitpacked, json, and undecided machines as text. 
it names these according to a scheme involving an "experiment name"
and outputs them every X machines, for a given number X. 
NAME_i_bin.bin 
NAME_i_json.json 
NAME_i_undecided.txt 
NAME_i_checkpoint.txt 

separately, there is a function which aggregates all the files from a run 
into a single file, and a function which prints out run statistics in various 
ways. 
-}

{-
TODO: 
make utility for running runnerDotPy from command line to make folder
make scripts to display files
make a tactic whose job it is to split up the tree
better rep for counts?
make vec n decodable (somehow?)
-}

--tactics, machines to run, experiment name (for filename), machines per "chunk", start file num
runnerDotPy :: V.Vector Tactic -> [Turing] -> Text -> Int -> Int -> IO ()
runnerDotPy tacticList startMachines experimentName chunkSize startFileNum
  = loop ((,0) <$> startMachines) [] startFileNum 0
  where
  filePrefix i = experimentName <> "_" <> show i <> "_"
  loop :: [(Turing, Int)]
    -- results obtained so far 
    -> [(Turing, Mystery TapeSymbol (SimResult InfCount))]
    -- next file to output
    -> Int
    -- total results output so far
    -> Int
    -> IO ()
  loop [] res i resCount = outputFiles (filePrefix i) experimentName i [] res resCount >> pure ()
  loop todos res@((>= chunkSize) . length -> True) i resCount = do
    newResCount <- outputFiles (filePrefix i) experimentName i (fst <$> todos) res resCount
    loop todos [] (i+1) newResCount
  loop ((tm, n) : todos) curRes i resCount
    = -- trace ("remTodo: " <> show (length todos)) $ -- <> " len res: " <> show (length curRes)) $ 
    -- trace ("machine: " <> showP tm <> "\n") $ 
    case tacticList V.!? n of
    -- TODO: how to get a "we failed" result / let's do a better one than this
    Nothing -> let newRes = Mystery $ Continue 0 (Phase 0) (initExpTape (Bit False)) 0 in
      loop todos ((tm, newRes) : curRes) i resCount
    Just (OneShot f) -> case f tm of
      Nothing -> loop ((tm, n+1): todos) curRes i resCount
      Just (Left e) -> let branchMachines = branchOnEdge e tm in
        loop (((,n) <$> branchMachines) ++ todos) curRes i resCount
      Just (Right r) -> loop todos ((tm, r) : curRes) i resCount
    Just (Simulation f) -> case f tm of
      (newTMs, newRes) -> --trace ("new tms: " <> show newTMs <> " newRes: " <> show newRes) $ 
        loop (((,n+1) <$> newTMs) ++ todos) (newRes ++ curRes) i resCount

--we use checkpoints with a checksum. the format is one short machine string per line, 
--then a final line with a number corresponding to the number of machiens in the file, 
--as a checksum to prevent bugs where the program is interrupted 
outputCheckpoint :: Text -> [Turing] -> IO ()
outputCheckpoint filePrefix machines = if null machines then pure () else do
  let numMachines = length machines
      chkptMessage = show numMachines <> " machines remain to do, saved in checkpoint" <> filePrefix <> "\n"
      chkptString = machinesToText machines <> show numMachines <> "\n"
  TLIO.writeFile (toString $ filePrefix <> "checkpoint.txt") $ fromStrict chkptString
  putText chkptMessage

--int parameter is previous count of results, int return val is next result count
outputFiles :: Text -> Text -> Int -> [Turing]
  -> [(Turing, Mystery TapeSymbol (SimResult InfCount))] -> Int -> IO Int
outputFiles filePrefix experimentName i todo results prevResCount = do
  let newResCount = prevResCount + length results
      msg = "writing " <> show (length results) <> " to disk\ntotal output so far: " <> show newResCount <> "\n"
  putText msg
  let binBuilder = bitPackResults results
      binFileName = toString $ filePrefix <> "bin.bin"
  --line copied from bytestrings 0.11 since we have 0.10;
  --should be written as "writeFile"
  withBinaryFile binFileName WriteMode (`hPutBuilder` binBuilder)
  TLIO.writeFile (toString $ filePrefix <> "json.json") $ resultsToText results
  TLIO.writeFile (toString $ filePrefix <> "undecided.txt") $
    fromStrict $ machinesToText $ getContinues results
  outputCheckpoint filePrefix todo
  -- (checkpointMachines, checkpointNum) <- loadNewestCheckpoint (toString experimentName)
  -- assertMsg 
  --   (null todo || (checkpointMachines, checkpointNum) == (todo, i)) 
  --   ("checkpoint failed! i, num:" <> show (i, checkpointNum) 
  --     <> "todo:" <> showP todo <> "\ncheckpoint: " <> showP checkpointMachines)
  pure newResCount

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
  , ("splitfast", splitterTacticVector V.++ fastTacticVector)
  , ("fewthings", splitterTacticVector V.++ basicTacticVector V.++ bwSearchTacticVector)
  ]
--sarah barrios thank god you introduced me to your sister

usageMessage :: Text
usageMessage = "usage: stack exec busy-beavers-exe experimentName tacticName chunkSize inputMachines"
  <> "\ninputMachines: either a .txt or seed_bit_stateCount\n"

extractCheckpointNumber :: String -> String -> Maybe Int
extractCheckpointNumber experimentName s = do
  let eFN = takeFileName experimentName <> "_"
      chpt :: String = "_checkpoint.txt"
  guard $ eFN `isPrefixOf` s
    && chpt `isSuffixOf` s
  let remS = drop (length eFN) s
  let remRemS = reverse $ drop (length chpt) $ reverse remS
  let intAns :: Int = U.read remRemS
  pure intAns

--the checkpoint filename to load. returns nothing if the checkpoint is not valid. 
loadCheckpoint :: String -> IO (Maybe [Turing])
loadCheckpoint fileName = do
  putTextLn $ "trying checkpoint: " <> fromString fileName <> "\n"
  fileContents <- TIO.readFile fileName
  let fileLines = lines fileContents
      mbMachinesAndNumber :: Either Text ([Turing], Int) = case fileLines of
        [] -> Left "file empty"
        (l : ls) -> do
          let (lastLine :| otherLines) = NE.reverse (l :| ls)
          let checksumReadFail = "last line of file was " <> lastLine <> " which is not an integer"
          checkNumber :: Int <- maybeToRight checksumReadFail $ readMaybe $ toString lastLine
          let machines = unm <$> reverse otherLines
              checksumValidateFail = "checksum was " <> show checkNumber <> " but length machines was " <> show (length machines)
          guardMsg (length machines == checkNumber) checksumValidateFail
          pure (machines, checkNumber)
  case mbMachinesAndNumber of
    Left err -> do
      putTextLn err
      pure Nothing
    Right (machines, checkNumber) -> do
      putTextLn $ "validated " <> show checkNumber <> " machines were present in checkpoint " <> fromString fileName
      pure $ Just machines

-- (a -> Maybe b) -> [a] -> Maybe b 
loadNewestCheckpoint :: String -> IO ([Turing], Int)
loadNewestCheckpoint experimentName = do
  dirContents <- listDirectory experimentDirectory
  let checkpointFiles = mapMaybe
        (\s -> (s,) <$> extractCheckpointNumber experimentName s)
        dirContents
      sortedCheckpointFiles = sortOn (Data.Ord.Down . snd) checkpointFiles
  putTextLn $ "found checkpoints: " <> show (snd <$> sortedCheckpointFiles)
  mbAns <- headMapMaybeM mbLoad sortedCheckpointFiles
  case mbAns of
    Nothing -> error "no checkpoint file was valid"
    Just ans -> pure ans
 where
  experimentDirectory = takeDirectory experimentName
  mbLoad (checkpointFn, checkpointNum) = (,checkpointNum+1) <$$> loadCheckpoint (experimentDirectory <> "/" <> checkpointFn)
  thing :: (a -> Maybe b) -> [a] -> Maybe b
  thing f ls = viaNonEmpty head $ mapMaybe f ls
  headMapMaybeM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
  headMapMaybeM f = \case
    [] -> pure Nothing
    (a : as) -> do
      mb <- f a
      case mb of
        Nothing -> headMapMaybeM f as
        Just b -> pure $ Just b
  headMapMaybeM2 :: forall m a b. (Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
  headMapMaybeM2 f = foldl' foldFunc (pure Nothing) where
    foldFunc :: m (Maybe b) -> a -> m (Maybe b)
    foldFunc mMb a = do
      maybeB <- mMb
      case maybeB of
        Just b -> pure $ Just b
        Nothing -> f a

--[turing] is list of machines. int is next file number to write
getMachines :: String -> String -> IO ([Turing], Int)
getMachines experimentName inputMachineString
  | ".txt" `isSuffixOf` inputMachineString
    = (,0) <$> loadMachinesFromFile inputMachineString
  | inputMachineString == "resume" = loadNewestCheckpoint experimentName
  | otherwise = case inputMachineString of
             ['s', 'e', 'e', 'd', '_', bit, '_', numStates] ->
               let machineFunc = case bit of
                     '0' -> startMachine0
                     '1' -> startMachine1
                     _ -> invalidStr
               in
               pure ([machineFunc (digitToInt numStates)], 0)
             _ -> invalidStr
  where
      invalidStr :: a
      invalidStr
        = error
            $ fromString
                $ inputMachineString <> " is not a valid machine string"

runnerDotPyFromArgs :: IO ()
runnerDotPyFromArgs = do
  args <- getArgs
  case args of
    [experimentName, tacticName, chunkSizeString, inputMachineString] -> do
        createDirectoryIfMissing True $ takeDirectory experimentName
        let chunkSize :: Int = U.read chunkSizeString
            tacticVec = tacticVectors ^?! ix tacticName
        (inputMachines, startNum) <- getMachines experimentName inputMachineString
        let inputMessage = "recieved " <> show (length inputMachines)
              <> " machines as input. running: " <> fromString tacticName
              <> " starting recording at file number: " <> show startNum <> "\n"
        putText inputMessage
        runnerDotPy tacticVec inputMachines (fromString experimentName) chunkSize startNum
        putText inputMessage
        aggregateFiles experimentName

    _ -> putText usageMessage

{-
a utility which takes an experiment's name, for each file type collects all the
files of that type and aggregates them into one file named with the prefix 
NAME_all
-}

aggregateTextFiles :: [FilePath] -> FilePath -> IO ()
aggregateTextFiles fnsIn fnOut = do
  allContents <- traverse TLIO.readFile fnsIn
  traverse_ (TLIO.appendFile fnOut) allContents

aggregateBinaryFiles :: [FilePath] -> FilePath -> IO ()
aggregateBinaryFiles fnsIn fnOut = do
  allContents <- traverse BL.readFile fnsIn
  traverse_ (BL.appendFile fnOut) allContents

aggregateFiles :: String -> IO ()
aggregateFiles experimentName = do
  let experimentDirectory = takeDirectory experimentName
      experimentFN = takeFileName experimentName
  dirContents <- listDirectory experimentDirectory
  let toAggregate = ((experimentDirectory <> "/") <>) <$>
        filter (\s -> experimentFN `isPrefixOf` s && not ((experimentFN <> "_all") `isPrefixOf` s))
        dirContents
  let binaryFiles = filter (\s -> "bin.bin" `isSuffixOf` s) toAggregate
  let jsonFiles = filter (\s -> "json.json" `isSuffixOf` s) toAggregate
  let undecidedFiles = filter (\s -> "undecided.txt" `isSuffixOf` s) toAggregate
  assert (length binaryFiles == length jsonFiles
    && length jsonFiles == length undecidedFiles)
    putText $ "aggregating " <> show (length binaryFiles) <> " files\n"
  aggregateBinaryFiles binaryFiles $ experimentName <> "_all_bin.bin"
  aggregateTextFiles jsonFiles $ experimentName <> "_all_json.json"
  aggregateTextFiles undecidedFiles $ experimentName <> "_all_undecided.txt"


-- popWord64FromBS :: BL.ByteString -> Maybe (Word64, BL.ByteString)
-- popWord64FromBS bs = if BL.null bs then Nothing else 
--   Just $ first () $ iterate getWord ([], bs) U.!! 8 where 
--     getWord :: ([Word8], BL.ByteString) -> ([Word8], BL.ByteString)
--     getWord (words, bs) = case BL.uncons bs of 
--       Nothing -> error "bytestring wrong length 3"
--       Just (newWord, newBS) -> (newWord : words, newBS)

getTMandResult :: Int -> Get (Turing, BitSimResult)
getTMandResult numStates = do
  tmWord64 <- getWord64be
  resWord8 <- getWord8
  resWord64 <- getWord64be
  pure (decodeTM numStates tmWord64,
        bitDecodeSimResult resWord8 resWord64)

getManyItem :: Get a -> Get [a]
getManyItem getOne = do
  consumedAll <- isEmpty
  if consumedAll
    then pure []
    else do
      nextOne <- getOne
      (nextOne :) <$> getManyItem getOne


-- popResultFromBS :: Int -> BL.ByteString 
--   -> Maybe ((Turing, BitSimResult), BL.ByteString)
-- popResultFromBS numStates bs = if BL.null bs then Nothing else
--   case popWord64FromBS bs of 
--   Nothing -> error "bs wrong length"
--   Just (tmWord64, bs1) -> case BL.uncons bs1 of 
--     Nothing -> error "bs wrong length 2"
--     Just (fstResWord8, bs2) -> case popWord64FromBS bs2 of 
--       Nothing -> error "bs wrong length 3"
--       Just (sndResWord64, bsLeftover) 
--         -> Just ((decodeTM numStates tmWord64, 
--                   bitDecodeSimResult fstResWord8 sndResWord64),
--                  bsLeftover)

loadBinaryFile :: Int -> FilePath -> IO [(Turing, BitSimResult)]
loadBinaryFile numStates fp = do
  rawBytestring <- BL.readFile fp
  --pure $ unfoldr (popResultFromBS numStates) rawBytestring
  pure $ runGet (getManyItem (getTMandResult numStates)) rawBytestring

loadResult :: Text -> (Turing, SomeResult)
loadResult textIn = trace (toString $ "loading: " <> textIn) $ let
  (tmText, jsonText) = T.breakOn " " textIn
  in trace (toString $ "jsontext: " <> jsonText)
    (unm tmText, fromJust . decode . toLazyByteString . encodeUtf8Builder $ jsonText)

loadJSONFile :: FilePath -> IO [(Turing, SomeResult)]
loadJSONFile fp = do
  lazyFile <- TLIO.readFile fp
  pure $ unfoldr parseNextLine lazyFile
  where
    parseNextLine :: TL.Text -> Maybe ((Turing, _), TL.Text)
    parseNextLine txt = if TL.null txt then Nothing else let
      (nextLine, remaining) = TL.span (/= '\n') txt
      in Just (loadResult $ toStrict nextLine, TL.tail remaining)


loadMachinesFromFile :: String -> IO [Turing]
loadMachinesFromFile fn = do
  putTextLn $ "loading machines from file: " <> fromString fn
  fileContents <- TIO.readFile fn
  let machines = unm <$> lines fileContents
  putTextLn $ "loaded " <> show (length machines) <> " machines"
  pure machines

--bitpacked machines, json machines, and undecided machines
loadAggregatedExperimentFiles :: Int -> String
  -> IO ([(Turing, BitSimResult)],
         [(Turing, SomeResult)],
         [Turing])
loadAggregatedExperimentFiles numStates experimentName = do
  bsrs <- loadBinaryFile numStates $ experimentName <> "_all_bin.bin"
  jsons <- loadJSONFile $ experimentName <> "_all_json.json"
  unfinished <- loadMachinesFromFile $ experimentName <> "_all_undecided.txt"
  pure (bsrs, jsons, unfinished)
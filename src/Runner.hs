module Runner where


import Relude
import Control.Lens
import qualified Relude.Unsafe as U
import qualified Data.Map as M
import qualified Data.Text as T (concat, intercalate)
import qualified Data.Set as S
import qualified Data.List.NonEmpty as NE
import Relude.Extra (bimapBoth)
import Prettyprinter
import Safe.Exact
import Control.Exception (assert)
import Safe.Partial

import Data.ByteString.Builder as BS
import Data.Bits
import qualified Data.ByteString.Lazy as BL

import qualified Data.Vector as V
import qualified Data.Text.Lazy.IO as TIO
import Util
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
    packLR s p t = assert (all (\x -> x >= 0 && x <= fromIntegral (maxBound :: Word16)) [s,p,t])
      (1, packWord16Word64 (fromIntegral s, fromIntegral p, fromIntegral t, 0))

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

--a series of lines, each line is first a machine string and then a json blob 
--containing the simulation result
resultsToText :: [(Turing, Mystery TapeSymbol (SimResult InfCount))] -> _
resultsToText results = toLazyText $ foldMap mkLine $ filter (not . resIsBin . snd) results where
  mkLine :: (Turing, Mystery TapeSymbol (SimResult InfCount)) -> _
  mkLine (m, Mystery res)
    = fromText (machineToNotation m <> " ") <> encodeToTextBuilder res <> fromText "\n"
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

--tactics, machines to run, experiment name (for filename), machines per "chunk"
runnerDotPy :: V.Vector Tactic -> [Turing] -> Text -> Int -> IO ()
runnerDotPy tacticList startMachines experimentName chunkSize
  = loop ((,0) <$> startMachines) [] 0
  where
  filePrefix i = experimentName <> "_" <> show i <> "_"
  loop :: [(Turing, Int)]
    -- results obtained so far 
    -> [(Turing, Mystery TapeSymbol (SimResult InfCount))]
    -- next file to output
    -> Int
    -> IO ()
  loop [] res i = outputFiles (filePrefix i) [] res
  loop todos res@((>= chunkSize) . length -> True) i = do
    outputFiles (filePrefix i) (fst <$> todos) res
    loop todos [] (i+1)
  loop ((tm, n) : todos) curRes i
    = -- trace ("remTodo: " <> show (length todos)) $ -- <> " len res: " <> show (length curRes)) $ 
    --trace ("machine: " <> showP tm <> "\n") $ 
    case tacticList V.!? n of
    -- TODO: how to get a "we failed" result / let's do a better one than this
    Nothing -> let newRes = Mystery $ Continue 0 (Phase 0) (initExpTape (Bit False)) 0 in
      loop todos ((tm, newRes) : curRes) i
    Just (OneShot f) -> case f tm of
      Nothing -> loop ((tm, n+1): todos) curRes i
      Just (Left e) -> let branchMachines = branchOnEdge e tm in
        loop (((,n) <$> branchMachines) ++ todos) curRes i
      Just (Right r) -> loop todos ((tm, r) : curRes) i
    Just (Simulation f) -> case f tm of
      (newTMs, newRes) -> loop (((,n+1) <$> newTMs) ++ todos) (newRes ++ curRes) i

outputFiles :: Text -> [Turing]
  -> [(Turing, Mystery TapeSymbol (SimResult InfCount))] -> IO ()
outputFiles filePrefix todo results = do
  let msg = "writing " <> show (length results) <> " to disk\n"
  putText msg
  let binBuilder = bitPackResults results
      binFileName = toString $ filePrefix <> "bin.bin"
  --line copied from bytestrings 0.11 since we have 0.10;
  --should be written as "writeFile"
  withBinaryFile binFileName WriteMode (`hPutBuilder` binBuilder)
  TIO.writeFile (toString $ filePrefix <> "json.json") $ resultsToText results
  TIO.writeFile (toString $ filePrefix <> "undecided.txt") $
    fromStrict $ machinesToText $ getContinues results
  if not (null todo) then do
      let chkptMessage = show (length todo) <> " machines remain to do, saved in checkpoint\n"
      putText chkptMessage
      TIO.writeFile (toString $ filePrefix <> "checkpoint.txt") $
        fromStrict $ machinesToText todo
    else pure ()

{-
a utility which takes an experiment's name, for each file type collects all the
files of that type and aggregates them into one file named with the prefix 
NAME_all
-}

aggregateTextFiles :: [FilePath] -> FilePath -> IO ()
aggregateTextFiles fnsIn fnOut = do
  allContents <- traverse TIO.readFile fnsIn
  traverse_ (TIO.appendFile fnOut) allContents

aggregateBinaryFiles :: [FilePath] -> FilePath -> IO ()
aggregateBinaryFiles fnsIn fnOut = do
  allContents <- traverse BL.readFile fnsIn
  traverse_ (BL.appendFile fnOut) allContents

aggregateFiles :: String -> IO ()
aggregateFiles experimentName = do
  let experimentDirectory = takeDirectory experimentName
  dirContents <- listDirectory experimentDirectory
  let toAggregate = ((experimentDirectory <> "/") <>) <$> 
        filter (\s -> takeFileName experimentName `isPrefixOf` s) dirContents
  let binaryFiles = filter (\s -> "bin.bin" `isSuffixOf` s) toAggregate
  let jsonFiles = filter (\s -> "json.json" `isSuffixOf` s) toAggregate
  let undecidedFiles = filter (\s -> "undecided.txt" `isSuffixOf` s) toAggregate
  assert (length binaryFiles == length jsonFiles
    && length jsonFiles == length undecidedFiles)
    putText $ "aggregating " <> show (length binaryFiles) <> " files\n"
  aggregateBinaryFiles binaryFiles $ experimentName <> "_all_bin.bin"
  aggregateTextFiles jsonFiles $ experimentName <> "_all_json.json"
  aggregateTextFiles undecidedFiles $ experimentName <> "_all_undecided.txt"



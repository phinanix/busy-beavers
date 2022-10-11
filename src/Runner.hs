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
import Data.Binary

import Util
import Count
import Skip
import ExpTape
import Turing
import TapeSymbol
import HaltProof
import SimulateSkip
import Graphs


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
assuming it is neither the first nor the second transition) which puts you to 43 bits. 
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

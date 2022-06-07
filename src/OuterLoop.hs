module OuterLoop where

import Relude hiding (inits)
import qualified Relude.Unsafe as Unsafe
import Control.Lens
import Data.List (maximumBy, foldl1, maximum, minimum)
import Data.List.NonEmpty (inits)

import Safe.Exact
import Prettyprinter
import Safe.Partial
import Control.Exception (assert)

import qualified Data.List.NonEmpty as NE ((<|))
import qualified Data.Set as S
import qualified Data.Vector as V

import Turing
import ExpTape
import Count
import HaltProof
import Results
import Glue
import SimulateSkip
import Skip
import Util
import Display
import SimulationLoops
import MoreSimulationLoops

{-
OneShot either fails, or hits an unknown edge requesting it to be defined (after 
which we will rerun the tactic), or gets to a result

Simulation has the ability to define edges itself (that's sort of hacky, but it's 
the best I've got for now). It defines some number of edges, as it desires, which 
"splits the world", and then for each "world" (each machine) it either fails to 
finish it, and returns it in the [Turing], or finishes it and returns it in the
second list. 
-}
data Tactic s = OneShot (Turing -> Maybe (Either Edge (SimResult InfCount s)))
              | Simulation (Turing -> ([Turing], [(Turing, SimResult InfCount s)]))

{-TODO: the whole point is to support tactics with more than one type of symbol
     my guess is we end up supporting this by substantially reworking the 
     "results" code / by having a symbol-type agnostic results type, which 
     might not actually be that significant a rework; there is other rework
     to do there too

TODO2: when a tactic fails, I think we want it to be able to say some things
  about why it failed (eg, I couldn't prove XYZ), and have those be carried 
  along with the machine. I think this could be a more general "write only 
  log" or something, but I'm not sure it makes sense to go straight there. 
  
-}
outerLoop :: forall s. (TapeSymbol s)
  => V.Vector (Tactic s) -> Turing -> [(Turing, SimResult InfCount s)]
outerLoop tacticList startMachine = loop [(startMachine, 0)] [] where
  -- the int is which tactic they are currently on
  loop :: [(Turing, Int)]
  -- results obtained so far 
      -> [(Turing, SimResult InfCount s)]
      -> [(Turing, SimResult InfCount s)]
  loop [] res = res
  loop ((tm, n) : todos) curRes = case tacticList V.!? n of
    -- TODO: how to get a "we failed" result / let's do a better one than this
    Nothing -> let newRes = Continue 0 (Phase 0) (initExpTape blank) 0 in
      loop todos ((tm, newRes) : curRes)
    Just (OneShot f) -> case f tm of
      Nothing -> loop ((tm, n+1): todos) curRes
      Just (Left e) -> let branchMachines = branchOnEdge e tm in
        loop (((,n) <$> branchMachines) ++ todos) curRes
      Just (Right r) -> loop todos ((tm, r) : curRes)
    Just (Simulation f) -> case f tm of
      (newTMs, newRes) -> loop (((,n+1) <$> newTMs) ++ todos) (newRes ++ curRes)

tacticBackwardSearch :: Tactic s
tacticBackwardSearch = OneShot (fmap (Right . ContinueForever) . backwardSearch)

--int is the limit on number of steps
--todo we want to be able to run something right before we give up
simLoop :: forall s. (TapeSymbol s)
  => Int
  -> NonEmpty (SimMultiAction s)
  -> Turing
  -> ([Turing], [(Turing, SimResult InfCount s)])
simLoop bigStepLimit updateFuncs startMachine 
  = loop (startMachine, 0, initSkipState startMachine) [] ([], [])
  where
  bigUpdateFunc :: Turing -> SimState s -> MultiResult s (SimState s)
  bigUpdateFunc machine = foldl1 (>=>) ((&) machine <$> updateFuncs)
  loop :: (Turing, Int, SimState s) -> [(Turing, Int, SimState s)]
    -> ([Turing], [(Turing, SimResult InfCount s)])
    -> ([Turing], [(Turing, SimResult InfCount s)])
  loop cur@(curMachine, curBigStep, curState) todo resSoFar@(unsolved, solved)
    = if curBigStep >= bigStepLimit
      then recurse todo (curMachine : unsolved, solved)
      else case bigUpdateFunc curMachine curState of
        NewState newState -> loop (curMachine, curBigStep + 1, newState) todo resSoFar
        Result result -> recurse todo (unsolved, (curMachine, result) : solved)
        UnknownEdge e -> let
          candidateMachines = branchOnEdge e curMachine
          in
          recurse ((makeNewState e cur <$> candidateMachines) <> todo) resSoFar
  makeNewState :: Edge -> (Turing, Int, SimState s) -> Turing -> (Turing, Int, SimState s)
  makeNewState edge (_oldM, bigStep, oldState) machine
    = (machine, bigStep, oldState & s_book %~ updateBook edge machine)
  recurse :: [(Turing, Int, SimState s)]
    -> ([Turing], [(Turing, SimResult InfCount s)])
    -> ([Turing], [(Turing, SimResult InfCount s)])
  recurse [] results = results
  recurse (next : todos) results = loop next todos results


basicSimLoop :: Tactic Bit 
basicSimLoop = Simulation $ simLoop 150 $ simulateStepPartial maxInt :| 
  (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist, 
  liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof
  ])

twoBitSimLoop :: Tactic TwoBit 
twoBitSimLoop = Simulation $ simLoop 50 $ simulateStepPartial maxInt :| 
  (liftOneToMulti <$> [checkSeenBefore
  , liftModifyState recordHist
  , liftModifyState recordDispHist
  , runAtCount 10 proveByLR
  , runAtCount 40 proveSimply
  , runAtCount 45 proveByInd
  ])
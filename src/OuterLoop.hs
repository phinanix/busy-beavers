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
import Data.Vector.Fixed.Unboxed

import qualified Data.List.NonEmpty as NE ((<|))
import qualified Data.Set as S
import qualified Data.Vector as V

import Turing
import Count
import HaltProof
import Results
import SimulateSkip
import TapeSymbol
import SimulationLoops
import MoreSimulationLoops
import SimulateTwoBit (TwoBit)
import Mystery
import ExpTape
import SimulateVecBit

{- 7 June 22 overall state
the tactics are coming along nicely, I'm super excited to have a TwoBit simulation tactic

the main remaining obstacle to using that to crush my enemies is that we currently aren't 
polymorphic over tactic types in outerloop, and to fix that we need to rework SimResult 
somewhat I think; or put it in a box that doesn't know about the type or something

relatedly, I would like to cleanup simresult. I think I would like to go through and make an 
explicit list of all the ways my program can prove a machine runs forever, and make HaltProof
exactly match that list. 

To generalize SimResult, it seems like what we need is essentially a tape-symbol agnostic way
to say "here is a tape we ended with", or "here is a skip". 
Which it seems like we can do with a wrapper type using an existential. 

A random other point is that it's going to be interesting figuring out how to make all the 
polymorphic things specialize when we don't have the output type. It seem like we'll probably 
just have to use VisibleTypeApplication. 

high priority todo: finish initBookTwoBit (it's very close I think) update: I had done this, 
but left the undefined one in a different file >>

-------- update end of day:
I did the MVP version of being polymorphic over tactic types, and thus have a very basic 
version working. 
12 machines of size 3 remain
checkboard (TT -> TF <-) II
goalpost (T^n -> TF^n <-) II
normal sweeper (???) TR1TR0FL2___FR0TL2 II(I - doublespeed)I
counter (TF / TT) I
both sides sweeper II
counter (T / F) ?? I
I figure the "counter machine TF/TT" not working is because I still need to get 
the "move one square, while staying in the same state, means you eat a whole RLE of symbols"
going, which is fine, I can just use chainArbitrary? Probably? if not I can definitely just
get that up easily enough. 

The confusing part is only the 2 checkerboards and the TF/TT counter depend on that, the 
other 9 unproven machines, should just be proveable? with current methods? which should eat
normal sweepers for breakfast and were specifically fine-tuned to beat counter machines. 
So I need more investigation about why they don't work for those. 

Other todos: the code is really slow for some reason :/. Displaying the results in a better
format is high priority, the current one is garbage. Run on n=4, since that often does a 
better job fuzzing than n=3, and also once n=3 works for real make n=4 work. Though if we 
hit all the above machines, I would think we'd get most of the n=4 stuff for free, not 100% 
of it. We'll at least need ThreeBit for full n=4, and I'll probably just go straight for k-bit
because that's going to have to happen eventually. 

midnight:08 update:
the 2 checkerboard and FF/FT counter, are the only two that remain after I put 
  , runAtCount 145 proveByLR
  , runAtCount 146 proveSimply
  , runAtCount 147 proveByInd
in the single bit tactics, previously those weren't there because I forgot >>
so everything is as expected and we're super close!
Also, I checked, and chainArbitrary handles some of what we need it to, but we need it to be
able to chain 

in 2 steps we turn
phase: 0  |>|FT|<|
into:
phase: 0 (|TT|, 1) |>

to make 

in 2x steps we turn
phase: 0  |>|FT|<| (|FT|, x)
into:
phase: 0 (|TT|, x + 1) |>

but it doesn't do that yet. Should be pretty straightforward to handle though

8 June 22 
Amanda suggests using colors in trace statements
Amanda, full of good ideas, suggested I write this down. I'm having a problem where 
  lastsize3 has the wrong induction hypothesis guessed, because it's using TwoBit Skips
  which mean that displacement isn't the right way to calculate what parts of the tape
  we have read (we need readshifts instead). I thought I rewrote that part of the code 
  (guessInductionHypothesis) to use readshifts instead of raw displacements, but I 
  haven't. After more investigation, I learned that I am (afaict) correctly tracking the 
  ReadShiftHistory, but then it just gets ignored by guessInductionHypothesis. It should
  be pretty straightforward to rewrite guessInductionHypothesis to append all the ReadShifts
  together instead of using the displacements. 
-}

{-
OneShot either fails, or hits an unknown edge requesting it to be defined (after 
which we will rerun the tactic), or gets to a result

Simulation has the ability to define edges itself (that's sort of hacky, but it's 
the best I've got for now). It defines some number of edges, as it desires, which 
"splits the world", and then for each "world" (each machine) it either fails to 
finish it, and returns it in the [Turing], or finishes it and returns it in the
second list. 
-}
data Tactic 
  = OneShot (Turing -> Maybe (Either Edge (Mystery TapeSymbol (SimResult InfCount))))
  | Simulation (Turing -> ([Turing], [(Turing, Mystery TapeSymbol (SimResult InfCount))]))

oneShot :: (TapeSymbol s) => (Turing -> Maybe (Either Edge (SimResult InfCount s))) -> Tactic 
oneShot f = OneShot $ fmap (fmap Mystery) . f

simulation :: (TapeSymbol s) 
  => (Turing -> ([Turing], [(Turing, SimResult InfCount s)])) -> Tactic
simulation f = Simulation $ fmap (fmap (fmap Mystery)) . f 

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
outerLoop :: V.Vector Tactic -> Turing -> [(Turing, Mystery TapeSymbol (SimResult InfCount))]
outerLoop tacticList startMachine = loop [(startMachine, 0)] [] where
  -- the int is which tactic they are currently on
  loop :: [(Turing, Int)]
  -- results obtained so far 
      -> [(Turing, Mystery TapeSymbol (SimResult InfCount))]
      -> [(Turing, Mystery TapeSymbol (SimResult InfCount))]
  loop [] res = res
  loop ((tm, n) : todos) curRes 
    = trace ("remTodo: " <> show (length todos)) $ -- <> " len res: " <> show (length curRes)) $ 
    case tacticList V.!? n of
    -- TODO: how to get a "we failed" result / let's do a better one than this
    Nothing -> let newRes = Mystery $ Continue 0 (Phase 0) (initExpTape (Bit False)) 0 in
      loop todos ((tm, newRes) : curRes)
    Just (OneShot f) -> case f tm of
      Nothing -> loop ((tm, n+1): todos) curRes
      Just (Left e) -> let branchMachines = branchOnEdge e tm in
        loop (((,n) <$> branchMachines) ++ todos) curRes
      Just (Right r) -> loop todos ((tm, r) : curRes)
    Just (Simulation f) -> case f tm of
      (newTMs, newRes) -> loop (((,n+1) <$> newTMs) ++ todos) (newRes ++ curRes)

tacticBackwardSearch :: Tactic
tacticBackwardSearch = oneShot @Bit (fmap (Right . ContinueForever) . backwardSearch)

--int is the limit on number of steps
--todo we want to be able to run something right before we give up
simLoop :: forall s. (TapeSymbol s)
  => Int
  -> NonEmpty (SimMultiAction s)
  -> Turing
  -> ([Turing], [(Turing, SimResult InfCount s)])
simLoop bigStepLimit updateFuncs startMachine 
  = simLoopFromTape bigStepLimit updateFuncs startMachine (Phase 0) (initExpTape blank)

simLoopFromTape :: forall s. (TapeSymbol s)
  => Int
  -> NonEmpty (SimMultiAction s)
  -> Turing
  -> Phase
  -> ExpTape s InfCount 
  -> ([Turing], [(Turing, SimResult InfCount s)])
simLoopFromTape bigStepLimit updateFuncs startMachine startPhase startTape
  = loop (startMachine, 0, skipStateFromPhTape startMachine startPhase startTape) [] ([], [])
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


basicSimLoop :: Tactic 
basicSimLoop = simulation $ simLoop 150 $ simulateStepPartial maxInt :| 
  (liftOneToMulti <$> [checkSeenBefore, liftModifyState recordHist, 
  liftModifyState recordDispHist,
  runIfCond (atLeftOfTape . view s_tape) attemptEndOfTapeProof,
  runIfCond (atRightOfTape . view s_tape) attemptOtherEndOfTapeProof
  , runAtCount 145 proveByLR
  , runAtCount 146 proveSimply
  , runAtCount 147 proveByInd
  ])

twoBitSimLoop :: Tactic
twoBitSimLoop = simulation @TwoBit $ simLoop 150 $ simulateStepPartial maxInt :| 
  (liftOneToMulti <$> [checkSeenBefore
  , liftModifyState recordHist
  , liftModifyState recordDispHist
  , runAtCount 10 proveByLR
  -- , runAtCount 40 proveSimply
  -- , runAtCount 45 proveByInd
  , runAtCount 145 proveByLR
  , runAtCount 146 proveSimply
  , runAtCount 147 proveByInd
  ])

twoBitDispLoop :: TapeSymbol s => Turing -> ([Turing], [(Turing, SimResult InfCount s)])
twoBitDispLoop = simLoop 150 $ simulateStepPartial maxInt :| 
  (liftOneToMulti <$> [
    liftModifyState recordHist
  , liftModifyState recordDispHist
  ])

baseSimLoop :: (TapeSymbol s) => Turing -> ([Turing],[(Turing, SimResult InfCount s)])
baseSimLoop = simLoop 150 $ simulateStepPartial maxInt :| 
  (liftOneToMulti <$> [checkSeenBefore
  , liftModifyState recordHist
  , liftModifyState recordDispHist
  , runAtCount 10 proveByLR
  , runAtCount 40 proveSimply
  , runAtCount 145 proveByLR
  , runAtCount 146 proveSimply
  , runAtCount 147 proveByInd
  ])

threeBitSimLoop :: Tactic
threeBitSimLoop = simulation @(Vec 3 Bit) baseSimLoop

fourBitSimLoop :: Tactic
fourBitSimLoop = simulation @(Vec 4 Bit) baseSimLoop

fiveBitSimLoop :: Tactic
fiveBitSimLoop = simulation @(Vec 5 Bit) baseSimLoop


basicTacticVector :: V.Vector Tactic 
basicTacticVector = V.fromList [basicSimLoop, twoBitSimLoop] --, tacticBackwardSearch]

threeFourFiveTacticVector :: V.Vector Tactic
threeFourFiveTacticVector = V.fromList [threeBitSimLoop, fourBitSimLoop, fiveBitSimLoop]

bwSearchTacticVector :: V.Vector Tactic
bwSearchTacticVector = V.fromList [tacticBackwardSearch]

countSimResType :: [Mystery TapeSymbol (SimResult c)] -> (Int, Int, Int, Int) 
countSimResType inp = foldr myPlus (0,0,0,0) (fmap whichCat inp) where 

  myPlus (a,b,c,d) (x,y,z,w) = (a+x, b+y, c+z, d+w)
  whichCat :: Mystery TapeSymbol (SimResult c) -> (Int, Int, Int, Int) 
  whichCat (Mystery f) = case f of 
    Halted _ _ -> (1,0,0,0)
    Continue _ _ _ _ -> (0,1,0,0)
    ContinueForever _ -> (0,0,1,0)
    MachineStuckRes -> (0,0,0,1)

getContinues :: [(Turing, Mystery TapeSymbol (SimResult c))] -> [Turing]
getContinues = fmap fst . filter isContinue where 
  isContinue :: (Turing, Mystery TapeSymbol (SimResult c)) -> Bool
  isContinue (_, Mystery (Continue {})) = True 
  isContinue _ = False 

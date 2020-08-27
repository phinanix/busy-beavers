module Simulate where

import Relude hiding (cycle)
import Control.Lens

import Beaver
import SimulateSimple (Steps, SimState, SimResult(..), HaltProof(..))

--Pieces: turing machines with unknown edges
-- a simulator that does the usual simulate forward, while branching on unknown edges, according to
-- certain symmetry
-- a more powerful infinity prover
-- a Results type and an aggregator that adds to the results

data PartialStepResult = Unknown Edge | Stopped Steps Dir Tape | Stepped Dir SimState

simStep:: Turing -> SimState -> PartialStepResult
simStep (Turing _ trans ) (i, steps, (Tape ls bit rs))
  = case trans ^. at (i, bit) of
    Nothing -> Unknown (i,bit)
    --we assume WLOG that the machine goes left and writes True when it halts
    Just Halt ->
      (Stopped (steps + 1) L $ tapeLeft $ Tape ls True rs)
    Just (Step j newBit L) ->
      (Stepped L (j, steps + 1, tapeLeft $ Tape ls newBit rs))
    Just (Step j newBit R) ->
      (Stepped R (j, steps + 1, tapeRight $ Tape ls newBit rs))

--the results should be
--  how many machines halted
--    the longest running N machines
--    the most ones N machines
--  how many ran forever, with which kind of proof
--  how many ran out of time
--  and keep a certain number thereof
data Results = Results
  { _haltCount :: Int
    , _longestRun :: (Int, Turing)
    , _mostOnes :: (Int, Turing)
  , _provenForever :: Int
    , _haltUnreachable :: Int
    , _cycle :: Int
    , _infinitySimple :: Int
    , _infinityN :: Int
  , _unproven :: Int
    , _unprovenExamples :: [(Turing, SimState)]
  }
$(makeLenses ''Results)

--number of unproven examples to keep
keepNum :: Int
keepNum = 20

addResult :: Turing -> SimResult -> Results -> Results
addResult turing (Halted steps tape) r =
  addHalter $ addLongest turing steps $ addOnesiest turing (ones tape) r where
    addLongest turing steps r = if steps > r ^. longestRun . _1
      then r & longestRun .~ (steps, turing) else r
    addOnesiest turing ones r = if ones > r ^. mostOnes . _1
      then r & mostOnes .~ (ones, turing) else r
    addHalter = haltCount +~ 1
addResult turing (ContinueForever proof) r =
  r & provenForever +~ 1 & proof2lens proof +~ 1 where
    proof2lens (HaltUnreachable _) = haltUnreachable
    proof2lens (Cycle _ _) = cycle
    proof2lens (OffToInfinitySimple _ _) = infinitySimple
    proof2lens (OffToInfinityN _ _) = infinityN
addResult turing (Continue state) r = let r' = r & unproven +~ 1 in
  if r' ^. unproven > keepNum then r'
    else r' & unprovenExamples %~ ((:) (turing,state))

branchOnEdge :: Edge -> Turing -> NonEmpty Turing
branchOnEdge e (Turing n m) = Turing n <$> addTrans <$> uniTrans n where
  addTrans t = m & at e ?~ t

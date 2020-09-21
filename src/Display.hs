module Display where

import Relude
import Control.Lens

import Turing
import Tape
import Simulate
import qualified Simple.Simulate as Simple (simulate, dispStartState, initState, SimResult(..))
import Simple.Display as Simple (dispResult)
import qualified Simple.Tape as Simple
import Data.Map (restrictKeys)

showOneMachine :: Turing -> Steps -> Text
showOneMachine t n =
  dispTuring t <> "\n" <> (mconcat $
  (\steps -> dispResult (Simple.simulate steps Simple.dispStartState t) <> "\n") <$>
  [0.. n]
  )

totalMachines :: Results a -> Int
totalMachines r = r ^. haltCount + r ^. provenForever + r ^. unproven

dispResults :: Results Tape -> Text
dispResults r = "checked: " <> show (totalMachines r) <> " machines.\n"
  <> show (r ^. haltCount) <> " machines halted\n"
  <> "the most steps was " <> show (r ^? longestRun . _Just . _1) <> ", performed by\n"
  <> maybe "None" dispTuring (r ^? longestRun . _Just . _2)
  <> "final tape: " <> show (fmap dispTape (r ^? mostOnes . _Just . _3)) <> "\n"
  <> "the most ones was " <> show (r ^? mostOnes . _Just . _1) <> ", performed by\n"
  <> maybe "None" dispTuring (r ^? mostOnes . _Just . _2)
  <> "final tape:" <> show (fmap dispTape (r ^? mostOnes . _Just . _3)) <> "\n"
  <> show (r ^. provenForever) <> " machines were proven to run forever\n"
  <> show (r ^. haltUnreachable) <> " by lack of halt-reachability\n"
  <> show (r ^. cycledCount) <> " by cycling\n"
  <> show (r ^. infinityN) <> " by running off the tape in a cycle\n"
  <> show (r ^. backwardSearches) <> " by backwards search\n"
  -- <> "including:\n" <> (mconcat $ dispTuring <$> r ^. backwardExamples)
  <> "\n"
  <> show (r ^. unproven) <> " machines were not proven to halt, including:\n"
  <> (mconcat $ dispUnproven <$> r ^. unprovenExamples)
  where
    dispUnproven :: (Turing, SimState Tape) -> Text
    dispUnproven (t, (SimState steps _ finalState)) = "after: " <> show steps <> " steps,\n"
      <> dispTuring t <> "\nwas not shown to halt or run forever\n"
      <> "final state: " <> dispTMState finalState <> "\n\n\n"

tnfSignature :: Steps -> Turing -> [Edge]
tnfSignature n t = ordNub duplicateEdgesList where
  stateList = (\steps -> Simple.simulate steps Simple.initState t) <$> [0.. n]
  getEdge :: Simple.SimResult -> Maybe Edge
  getEdge (Simple.Continue (phase, _, Simple.Tape _ point _)) = Just $ (phase, point)
  getEdge _ = Nothing
  duplicateEdgesList = (Phase 0, False) : mapMaybe getEdge stateList

tnfPrecursors :: Steps -> Turing -> [Turing]
tnfPrecursors steps t@(Turing n trans) = Turing n <$> restrictKeys trans <$> edgeSets where
  signature = tnfSignature steps t
  edgeSets :: [Set Edge]
  edgeSets = fromList <$> (drop 1 $ inits signature)

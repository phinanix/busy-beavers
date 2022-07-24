module Display where

import Relude
import Control.Lens
import qualified Data.Text as T
import Prettyprinter

import Turing
import Notation 
import ExpTape
import Results
import qualified Simple.Simulate as Simple (simulate, dispStartState, initState, SimResult(..))
import qualified Simple.Display as Simple (dispResult)
import qualified Simple.Tape as Simple
import Data.Map (restrictKeys)
import TapeSymbol
import SimulateSkip ( simulateOneTotalMachine )
import Count
import Numeric (showFFloat)
import Util
import OuterLoop
import SimulationLoops
import Tape

tapeToSimpleTape :: Tape Bit -> Simple.Tape
tapeToSimpleTape (Tape.Tape ls p rs) = Simple.Tape ls p rs 

flattenTape :: (TapeSymbol s) => Tape s -> Tape Bit 
flattenTape (Tape ls p rs) = Tape (bind toBits ls) newP (firstRs <> restRs) where 
  (newP : firstRs) = toBits p 
  restRs = bind toBits rs

showOneMachineTape :: Turing -> Steps -> Phase -> Simple.Tape -> Text 
showOneMachineTape t n p tape = 
  dispTuring t <> "\n" <> foldMap
  (\steps -> Simple.dispResult (Simple.simulate steps startState t) <> "\n")
  [0.. n]
  where 
    startState = (p, 0, tape)

showOneMachine :: Turing -> Steps -> Text
showOneMachine t n =
  dispTuring t <> "\n" <> foldMap
  (\steps -> Simple.dispResult (Simple.simulate steps Simple.dispStartState t) <> "\n")
  [0.. n]

execMachine :: Turing -> Steps -> IO ()
execMachine t n = putText $ showOneMachine t n 

dispPhaseET :: (Phase, ExpTape Bit InfCount) -> Text
dispPhaseET (ph, et) = "" <> dispPhase  ph <> ", " <> dispExpTape et <> "\n"

displayHist :: [(Phase, ExpTape Bit InfCount)] -> Text
displayHist hist = T.concat $ dispPhaseET <$> hist

displaySkipSimStep :: Turing -> Steps -> Doc ann
displaySkipSimStep t steps = dispResult $ SimulateSkip.simulateOneTotalMachine steps t ^. _2

displaySkipSimulation :: Turing -> Steps -> Doc ann
displaySkipSimulation t limit =
  prettyText (dispTuring t <> "\n") <> foldMap (\i -> displaySkipSimStep t i <> "\n") [0 .. limit]

displaySkipStepAndSkip :: Turing -> Steps -> Doc ann
displaySkipStepAndSkip t limit = case SimulateSkip.simulateOneTotalMachine limit t of
  (lastSkip : _, res) -> dispResult res <> "\nresulted from the skip:" <> show (pretty lastSkip)
  ([], res) -> error ("there were no skips for some reason, res:\n" <> show res)

displaySkipSimulationWithSkips :: Turing -> Steps -> Doc ann
displaySkipSimulationWithSkips t limit =
  prettyText (dispTuring t <> "\n") <> foldMap (\i -> displaySkipStepAndSkip t i <> "\n") [1.. limit]

-- temporarily removed due to maintainence or something
-- displayGlueStepAndSkip :: Turing -> Steps -> Bool -> Doc ann 
-- displayGlueStepAndSkip t limit displayBook = case SimulateSkip.simulateOneMachineByGluing limit t (initSkipState t) of 
--   ([], _book, res) -> error ("there were no skips for some reason, res:\n" <> show res)
--   (_, _book, Left e) -> error $ "I think you meant to simulate a total machine but " <> 
--       show e <> " was not a defined edge"
--   (lastSkip : _, book, Right res) -> dispResult dispExpTape res <> "\nresulted from the skip:" <> show (pretty lastSkip) 
--     <> "\n" <> if displayBook then pretty book else ""

-- displayGlueSimulationAndBook :: Turing -> Steps -> Doc ann 
-- displayGlueSimulationAndBook t limit = prettyText (dispTuring t <> "\n") 
--   <> foldMap (\i -> displayGlueStepAndSkip t i False <> "\n") [1.. limit-1]
--   <> displayGlueStepAndSkip t limit True 


totalMachines :: Results c s -> Int
totalMachines r = r ^. haltCount + r ^. provenForever + r ^. unproven

dispUnprovenFraction :: Results c s -> Text
dispUnprovenFraction r = fromString $
  (showFFloat (Just 2) $ fromIntegral (100 * r ^. unproven) / fromIntegral (r^. provenForever + r^. unproven))  ""

dispResults :: (Pretty s, Pretty c, Show s, Show c) => Results c s -> Text
dispResults r = "checked: " <> show (totalMachines r) <> " machines.\n"
  <> show (r ^. haltCount) <> " machines halted\n"
  <> "the most steps was " <> show (r ^? longestRun . _Just . _1) <> ", performed by\n"
  <> maybe "None" dispTuring (r ^? longestRun . _Just . _2)
  <> "final tape: " <> show (fmap showP (r ^? mostOnes . _Just . _3)) <> "\n"
  <> "the most ones was " <> show (r ^? mostOnes . _Just . _1) <> ", performed by\n"
  <> maybe "None" dispTuring (r ^? mostOnes . _Just . _2)
  <> "final tape:" <> show (fmap showP (r ^? mostOnes . _Just . _3)) <> "\n"
  <> show (r ^. provenForever) <> " machines were proven to run forever\n"
  <> show (r ^. haltUnreachable) <> " by lack of halt-reachability\n"
  <> show (r ^. cycledCount) <> " by cycling\n"
  <> show (r ^. infinityN) <> " by running off the tape in a cycle\n"
  <> show (r ^. backwardSearches) <> " by backwards search\n"
  -- <> "including:\n" <> (mconcat $ dispTuring <$> r ^. backwardExamples)
  <> show (r ^. skipInfinity) <> " by a skip to infinity\n"
  <> "\n"
  <> show (r ^. unproven) <> " machines were not proven to halt ("
  <> dispUnprovenFraction r <> "%), including:\n"
  <> (mconcat $ dispUnproven <$> r ^. unprovenExamples)
  where
    --dispUnproven :: (Turing, Steps, Phase, a) -> Text
    dispUnproven (t, steps, p, finalTape) = "after: " <> show steps <> " steps,\n"
      <> dispTuring t <> "\nwas not shown to halt or run forever\n"
      <> "final state: phase: " <> dispPhase p <> " tape: " <> showP finalTape <> "\n\n"

tnfSignature :: Steps -> Turing -> [Edge]
tnfSignature n t = ordNub duplicateEdgesList where
  stateList = (\steps -> Simple.simulate steps Simple.initState t) <$> [0.. n]
  getEdge :: Simple.SimResult -> Maybe Edge
  getEdge (Simple.Continue (phase, _, Simple.Tape _ point _)) = Just (phase, point)
  getEdge _ = Nothing
  duplicateEdgesList = (Phase 0, Bit False) : mapMaybe getEdge stateList

tnfPrecursors :: Steps -> Turing -> [Turing]
tnfPrecursors steps t@(Turing n trans) = Turing n <$> restrictKeys trans <$> edgeSets where
  signature = tnfSignature steps t
  edgeSets :: [Set Edge]
  edgeSets = fromList <$> (drop 1 $ inits signature)

dispSkipBook :: SkipBook Bit -> Text
dispSkipBook skips = foldMap (\s -> show (pretty s) <> "\n") $ fold skips

displayMacro :: (TapeSymbol s) => Int -> Turing -> Phase -> ExpTape s InfCount -> Int  
displayMacro limit machine startPhase startTape = length newM + length provedM where 
  (newM, provedM) = simLoopFromTape limit actions machine startPhase startTape
  actions = simulateStepPartial maxInt :| 
    (liftOneToMulti <$> [
      liftModifyState recordHist
    , liftModifyState recordDispHist
    ])
  
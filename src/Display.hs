module Display where
--functions for displaying my types nicely

import Control.Lens
import Relude hiding (state)
import Relude.Unsafe as Unsafe (init, last)

import Beaver
import SimulateSimple


showInt3Wide :: Int -> String
showInt3Wide i@((\i -> i < 10) -> True) = "  " <> show i
showInt3Wide i@((\i -> i < 100) -> True) = " " <> show i
showInt3Wide i = show i

dispBit :: Bit -> String
dispBit False = "0"
dispBit True = "1"

dispEdge :: Edge -> String
dispEdge (p, b) = show p <> " " <> show b

dispTrans :: Trans -> String
dispTrans Halt = "Halt"
dispTrans (Step p b d) = show p <> " " <> show b <> " " <> show d

dispET :: Edge -> Trans -> String
dispET e t = dispEdge e <> " | " <> dispTrans t <> "\n"

dispTuring :: Turing -> String
dispTuring (Turing states transitions) = (ifoldMap dispET transitions) <> "\n"

dispTape :: Tape -> String
dispTape (Tape ls h rs) = dispBits (reverse ls) <> ">" <> dispBit h <> "<" <> dispBits rs where
  dispBits :: [Bit] -> String
  dispBits [] = ""
  dispBits bits = mconcat ((\i -> dispBit i <> " ") <$> Unsafe.init bits)
    <> dispBit (Unsafe.last bits)

dispSimState :: SimState -> String
dispSimState (phase, steps, tape) = "step: " <> showInt3Wide steps
  <> " state: " <> show phase
  <> " tape: " <> dispTape tape

dispResult :: SimResult -> String
dispResult (Unknown edge) = "Edge: " <> show edge <> " was unknown"
dispResult (Stop steps tape) = "After " <> show steps
  <> " steps, the machine halted with the tape: \n" <> dispTape tape
dispResult (Continue state) = "continue: " <> dispSimState state
dispResult (ContinueForever proof) = "we proved the machine will go forever via: " <> show proof

showOneMachine :: Turing -> Steps -> String
showOneMachine t n = dispTuring t <> "\n" <> (mconcat $
  (\steps -> dispResult (simulate steps dispStartState t `evalState` 0) <> "\n") <$>
  [0.. n]
  )

--
aggregateResults :: Foldable t => t (Turing, SimResult) -> Steps -> String
aggregateResults rs simSteps = case foldr count (0::Int,[],[],[]) rs of
  (u,s,c,f) -> dispHalts s <> "\n" <> dispContinues c <> "\n" <> dispForevers f <> "\n"
    <> show u <> " machines hit an unknown edge"
  where
  count (_, Unknown _) (a,b,c,d) = (a+1, b, c, d)
  count (t, Stop steps tape) (a,b,c,d) = (a, (t,steps,tape):b, c, d)
  count (t, ContinueForever proof) (a,b,c,d) = (a,b,c, (t,proof):d)
  count (t, Continue state) (a,b,c,d) = (a, b, (t,state):c, d)
  dispHalts :: [(Turing, Steps, Tape)] -> String
  dispHalts halts =
    let
    numHalted = length halts
    --TODO :: don't store this in memory to avoid memory leak!
    longestRun = take 10 $ sortOn (Down . view _2) halts
    mostOnes = take 10 $ sortOn (Down . ones . view _3) halts
    in
    show numHalted <> " machines halted, with the most steps being: "
    -- <> (show $ view _2 <$> take 1 longestRun) <> " and the most ones being: " <>
    -- (show $ ones . view _3 <$> take 1 mostOnes) <> " by the respective machines:\n" <>
    -- (show $ view _1 <$> take 1 longestRun) <> "\n\n" <> (show $ view _1 <$> take 1 mostOnes) <>
    -- "\nthe longest run machines were: " <>
    -- (show $ view _2 <$> longestRun) <> "\nand the most ones were:" <>
    -- (show $ ones . view _3 <$> mostOnes)

  dispContinues :: [(Turing, SimState)] -> String
  dispContinues states = show (length states) <> " machines had not halted after "
    <> show simSteps <> " steps\n"
    <> mconcat (--(\i -> show i <> "\n")
                (\(t,s) -> dispTuring t <> "\n" <> dispSimState s <> "\n\n")
                <$> takeNeveryM 5 5 states)
  dispForevers :: [(Turing, HaltProof)] -> String
  dispForevers proofs = case foldr sortProofs ([],[],[],[]) proofs of
    (noHalts, cycles, simpleInfs, complexInfs)
      -> show (length proofs) <> " machines were proven to run forever\n"
      <> show (length noHalts) <> " by the halt state's unreachability\n"
      <> show (length cycles) <> " by the machine cycling\n"
      <> show (length simpleInfs)
      <> " by the machine going off one end of the tape in one state forever\n"
      <> show (length complexInfs)
      <> " by the machine going off one end of the tape in a short cycle forever\n"
  --TODO :: rewrite this to use _2 etc. from lens so the tuple is polymorphic
  --TODO :: figure out if there's some partition function that will do this automatically
  sortProofs p@(_, HaltUnreachable _) (nhs, cs, infs, infsC) = (p:nhs, cs, infs, infsC)
  sortProofs p@(_, Cycle _ _) (nhs, cs, infs, infsC) = (nhs, p:cs, infs, infsC)
  sortProofs p@(_, OffToInfinitySimple _ _) (nhs, cs, infs, infsC) = (nhs, cs, p:infs, infsC)
  sortProofs p@(_, OffToInfinityN _ _) (nhs, cs, infs, infsC) = (nhs, cs, infs, p : infsC)
--
ones :: Tape -> Int
ones (Tape ls h rs) = length $ filter (==True) $ ls <> rs <> [h]

takeNeveryM :: Int -> Int -> [a] -> [a]
takeNeveryM n m xs = go n m 0 xs where
  go :: Int -> Int -> Int -> [a] -> [a]
  go _ _ _ [] = []
  go 0 _ _ _ = []
  go n m 0 (x : xs) = x : go (n - 1) m 1 xs
  go n m i (_ : xs) = go n m ((i+1) `mod` m) xs

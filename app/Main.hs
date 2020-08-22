module Main where

import Relude
import Relude.Unsafe as Unsafe
import Control.Lens

import Beaver
import HaltProof

aggregateResults :: Foldable t => t (Turing, SimResult) -> Steps -> String
aggregateResults rs steps = case foldr count (0,[],[],[]) rs of
  (u,s,c,f) -> dispHalts s <> "\n" <> dispContinues c <> "\n" <> dispForevers f <> "\n"
    <> show u <> " machines hit an unknown edge"
  where
  count (t, Unknown _) (a,b,c,d) = (a+1, b, c, d)
  count (t, Stop steps tape) (a,b,c,d) = (a, (t,steps,tape):b, c, d)
  count (t, ContinueForever proof) (a,b,c,d) = (a,b,c, (t,proof):d)
  count (t, Continue state) (a,b,c,d) = (a, b, (t,state):c, d)
  dispHalts :: [(Turing, Steps, Tape)] -> String
  dispHalts halts =
    let
    numHalted = length halts
    --longestRun = take 10 $ sortOn (Down . fst) halts
    longestRun = take 10 $ sortOn (Down . view _2) halts
    mostOnes = take 10 $ sortOn (Down . ones . view _3) halts
    in
    show numHalted <> " machines halted, with the most steps being: " <>
    (show $ view _2 <$> take 1 longestRun) <> " and the most ones being: " <>
    (show $ ones . view _3 <$> take 1 mostOnes) <> " by the respective machines:\n" <>
    (show $ view _1 <$> take 1 longestRun) <> "\n\n" <> (show $ view _1 <$> take 1 mostOnes) <>
    "\nthe longest run machines were: " <>
    (show $ view _2 <$> longestRun) <> "\nand the most ones were:" <>
    (show $ ones . view _3 <$> mostOnes)
  ones :: Tape -> Int
  ones (Tape ls h rs) = length $ filter (==True) $ ls <> rs <> [h]
  dispContinues :: [(Turing, SimState)] -> String
  dispContinues states = show (length states) <> " machines had not halted after "
    <> show steps <> " steps\n"
    <> ((\s -> s <> "\n\n") . show <$> take 2 $ states)
  dispForevers :: [(Turing, HaltProof)] -> String
  dispForevers proofs = case foldr sortProofs ([],[],[]) proofs of
    (noHalts, cycles, simpleInfs)
      -> show (length proofs) <> " machines were proven to run forever\n"
      <> show (length noHalts) <> " by the halt state's unreachability\n"
      <> show (length cycles) <> " by the machine cycling\n"
      <> show (length simpleInfs)
      <> " by the machine going off one end of the tape in one state forever\n"
  sortProofs p@(t, HaltUnreachable _) (nhs, cs, infs) = (p:nhs, cs, infs)
  sortProofs p@(t, Cycle _ _) (nhs, cs, infs) = (nhs, p:cs, infs)
  sortProofs p@(t, OffToInfinitySimple _ _) (nhs, cs, infs) = (nhs, cs, p:infs)

bb2 :: Turing
bb2 = Turing {states = 2, transitions = fromList
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) True L)
  ,((Phase {unPhase = 0},True),Step (Phase {unPhase = 1}) True R)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 1},True),Halt)
  ]}

loop2 :: Turing
loop2 = Turing {states = 2, transitions = fromList
  --should step left and right forever
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) False R)
  --these two don't matter
  ,((Phase {unPhase = 0},True),Halt) --Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 1},True),Halt)
  ]}

main :: IO ()
main = do
  let machines = uniTuring 2
      simSteps = 30
      results = (\t -> (t,
        simulateHalt simSteps t `evalState` 0)) <$> machines
      sims = flip evalState 0 $ flip simulateHalt loop2 10
  --print sims
  putStrLn $ aggregateResults results simSteps
  print $ testHalt initState bb2

  --for_ [0.. 30] (\i -> print $ testHalt initState $ Unsafe.head $ drop i $ toList $ uniTuring 1)
  --print $ Unsafe.head $ drop 0 $ toList $ uniTuring 1
  --print $ Unsafe.head $ drop 6 $ toList $ uniTuring 1

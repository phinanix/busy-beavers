module Main where

import Relude hiding (state)
import Relude.Unsafe as Unsafe
import Control.Lens

import Beaver
import SimulateSimple
import Display

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

--this halted after a bit more time to simulate the OffToInfinityN proof
not_halt3 :: Turing
not_halt3 = Turing {states = 3, transitions = fromList [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L),((Phase {unPhase = 0},True),Halt),((Phase {unPhase = 1},False),Step (Phase {unPhase = 0}) True R),((Phase {unPhase = 1},True),Step (Phase {unPhase = 2}) False L),((Phase {unPhase = 2},False),Step (Phase {unPhase = 1}) True R),((Phase {unPhase = 2},True),Step (Phase {unPhase = 0}) True L)]}

--woah, this is a counting machine !!!
weird3 :: Turing
weird3 = Turing {states = 3, transitions = fromList
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 1}) False L)
  ,((Phase {unPhase = 0},True) ,Step (Phase {unPhase = 0}) False R)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 2}) True L)
  ,((Phase {unPhase = 1},True ),Halt)
  ,((Phase {unPhase = 2},False),Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 2},True ),Step (Phase {unPhase = 2}) True L)
  ]}

almostweird3 :: Turing
almostweird3 = Turing {states = 3, transitions = fromList
  [((Phase {unPhase = 0},False),Step (Phase {unPhase = 2}) False L)
  ,((Phase {unPhase = 0},True) ,Step (Phase {unPhase = 0}) False R)
  ,((Phase {unPhase = 1},False),Step (Phase {unPhase = 2}) True L)
  ,((Phase {unPhase = 1},True ),Halt)
  ,((Phase {unPhase = 2},False),Step (Phase {unPhase = 0}) True R)
  ,((Phase {unPhase = 2},True ),Step (Phase {unPhase = 2}) True L)
  ]}

main :: IO ()
main = do
  let machines = uniTuring 3
      simSteps = 50
      results = (\t -> force (t,
        simulateHalt simSteps t)) <$> machines
  putStrLn $ aggregateResults results simSteps
  --print $ testHalt initState bb2
  --putStrLn $ showOneMachine almostweird3 201

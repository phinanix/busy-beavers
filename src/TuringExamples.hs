module TuringExamples where

import Relude ( IsList(fromList), Bool(True, False) )

import Turing

--woah, this is a counting machine !!!
weird3 :: Turing
weird3 = Turing {states = 3, transitions = fromList
  [((Phase 0,False),Step (Phase 1) False L)
  ,((Phase 0,True) ,Step (Phase 0) False R)
  ,((Phase 1,False),Step (Phase 2) True L)
  ,((Phase 1,True ),Halt)
  ,((Phase 2,False),Step (Phase 0) True R)
  ,((Phase 2,True ),Step (Phase 2) True L)
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

fullsim_not_halt3 :: Turing
fullsim_not_halt3 = Turing {states = 3, transitions = fromList
  [((Phase 0,False),Step (Phase 1) True  R)
  ,((Phase 0,True ),Step (Phase 2) False R)
  ,((Phase 1,False),Step (Phase 2) False L)
  ,((Phase 1,True ),Step (Phase 0) True  L)
  ,((Phase 2,True ),Step (Phase 0) True  L)
  ]}

--0 False | 1 True R\n0 True | Halt\n1 False | 1 True L\n1 True | 2 False L\n2 False | 0 True R\n2 True | 2 True R\n
bb3 :: Turing
bb3 = Turing {states = 3, transitions = fromList
  [((Phase 0, False), Step (Phase 1) True R)
  ,((Phase 0, True ), Halt)
  ,((Phase 1, False), Step (Phase 2) False R)
  ,((Phase 1, True ), Step (Phase 1) True  R)
  ,((Phase 2, False), Step (Phase 2) True  L)
  ,((Phase 2, True ), Step (Phase 0) True  L)
  ]}

simple_sweeper :: Turing
simple_sweeper = Turing {states = 3, transitions  = fromList
  [((Phase 0, False), Step (Phase 1) True R)
  ,((Phase 1, False), Step (Phase 2) False L)
  ,((Phase 1, True), Step (Phase 1) False R)
  ,((Phase 2, False), Step (Phase 2) True L)
  ,((Phase 2, True), Step (Phase 0) True L)
  ]}


checkerboardSweeper :: Turing
checkerboardSweeper = Turing {states = 3, transitions  = fromList
  [((Phase 0, False), Step (Phase 1) True R)
  ,((Phase 0, True), Step (Phase 2) False L)
  ,((Phase 1, False), Step (Phase 2) False L)
  ,((Phase 1, True), Step (Phase 0) True R)
  ,((Phase 2, False), Halt)
  ,((Phase 2, True), Step (Phase 0) True L)
  ]}

goesLeftForever :: Turing
goesLeftForever = Turing {states = 2, transitions = fromList
  [((Phase 0, False), Step (Phase 1) True L)
--  ,((Phase 0, True), Step (Phase 0) False L)
  ,((Phase 1, False), Step (Phase 0) True L)
  ,((Phase 1, True), Halt)
  ]}

-- a four state binary counter which uses TF and TT as its digits 
binaryCounterTFTT :: Turing
binaryCounterTFTT = Turing {states = 4, transitions = fromList
  [((Phase 0,False),Step (Phase 1) True R)
  ,((Phase 0,True),Step (Phase 0) True R)
  ,((Phase 1,False),Step (Phase 2) False L)
  ,((Phase 1,True),Step (Phase 0) False R)
  ,((Phase 2,True),Step (Phase 3) False L)
  ,((Phase 3,False),Step (Phase 0) True L)
  ,((Phase 3,True),Step (Phase 2) True L)
  ]}
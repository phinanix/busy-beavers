module TuringExamples where

import Relude

import Turing
import Count
import Skip
import Test.QuickCheck
import Notation
import Util

--woah, this is a counting machine !!!
weird3 :: Turing
weird3 = unm "FL1FR0TL2TLHTR0TL2" 

counterIndHyp :: Config Count Bit 
-- 2 (F, n) >T< T F 
-- eg @ step 100
-- the thing we hope it goes to is
-- 0 (T, n) >T< T F 
-- eg @ step 170
counterIndHyp = Config (Phase 2) [(False, symbolVarCount (SymbolVar 0) 1)] True [(True, One), (False, One)]

counterIndHypReal :: Config Count Bit 
-- 2 F T (F, n) >T< T F 
-- eg @ step 100
-- the thing we hope it guesses is
-- 2 (F, n) >T< T F 
-- 0 (T, n) >T< T F 
-- eg @ step 170
--note that it needs to ignore the stuff that "doesn't matter"
counterIndHypReal = Config (Phase 2) [(False, symbolVarCount (SymbolVar 0) 1), (True, One), (False, One)] True [(True, One), (False, One)]

almostweird3 :: Turing
almostweird3 = unm "FL2FR0TL2TLHTR0TL2" 

fullsim_not_halt3 :: Turing
fullsim_not_halt3 = unm "TR1FR2FL2TL0___TL0"

--0 False | 1 True R\n0 True | Halt\n1 False | 1 True L\n1 True | 2 False L\n2 False | 0 True R\n2 True | 2 True R\n
bb3 :: Turing
bb3 = unm "TR1TLHFR2TR1TL2TL0"

simple_sweeper :: Turing
simple_sweeper = unm "TR1___FL2FR1TL2TL0"


checkerboardSweeper :: Turing
checkerboardSweeper = unm "TR1FL2FL2TR0TLHTL0"

goesLeftForever :: Turing
goesLeftForever = unm "TL1___TL0TLH"

-- a four state binary counter which uses TF and TT as its digits 
binaryCounterTFTT :: Turing
binaryCounterTFTT = unm "TR1TR0FL2FR0___FL3TL0TL2"

{-
as written on 27 Dec 2021, this machine broke guessInductionHypothesis 
it's a mildly complicated but not insane machine which has 4 phases:
1) scan all the way to the left of the block of trues, add a T to the block (phase 0)
2) inch your way right across the block of trues, dragging a single false along 
  with you (phases 0, 1, 3)
3) either, 
    arrive on the rightmost True in phase 0 or 1, 
      in which case don't add anything to the block and go to 1)
    arrive on the rightmost True in phase 3, in which case do some complicated end effect, 
      which uses phase 2 (and 0,1,3) and adds 3 T to the block 
which phase you arrive at the right of the block in presumably depends on some modular 
fact about the current length of the block
3T -> P1 
4T -> P3
8T -> P3
12T -> P3
so actually you are in a cycle after step 22 once the block grows to size 4
The interesting thing about this machine, is it adds symbols in blocks of 4, but not in a 
grid-aligned way; if you start out with eg 3 blocks of 4 (12), it adds 4 more trues, but 
1 on the left and 3 on the right. so dealing with this machine would either have to be 
somehow not requiring symbols to be grid aligned, or it would require the program to have a 
"grid shift" operation, which does seem possible to support. 
-}
machineBreaksIndGuess :: Turing 
machineBreaksIndGuess = unsafeFromRight $ nm "TR1TL0FR2TR3TR3___FL0FR0"

{-
for some reason this machine gets the result "machineStuck" when run alone in indProveLoop which
makes no sense
the general deal with this machine is it is Lin recurrent but has a fairly long cycle time 
(249 -> 379) (add 130)
predict 379 -> 509 (check)
predict-maybe 119 -> 249 (check)
with the pattern being (T, 9) F >F< 
producing (F, 2) (T, 4) of garbage to the right each time
Lin recurrence: check every 20, 100, 500 -> x5 each time?
-}
machineStuckMachine :: Turing
machineStuckMachine = unsafeFromRight $ nm "TR1FL0FR2___TL2TL3FR0TL0"

--I think this fails to be self glued basically because it assumes that x_0 is the same as x_0 in a different skip 
--which is kind of nonsense
thingWhichShouldBeSelfGlued :: Skip Count Bit 
thingWhichShouldBeSelfGlued = Skip {_start = Config {_cstate = (Phase 2), _ls = [(False,Count 1 (fromList []) (fromList []))], _c_point = False, _rs = [(True,Count 0 (fromList []) (fromList [(BoundVar 0,Sum {getSum = 1})])),(False,Count 1 (fromList []) (fromList []))]}, _end = EndMiddle (Config {_cstate = (Phase 2), _ls = [], _c_point = False, _rs = [(True,Count 1 (fromList []) (fromList [(BoundVar 0,Sum {getSum = 1})])),(False,Count 1 (fromList []) (fromList []))]}), _hops = Count 0 (fromList []) (fromList []), _halts = False, _displacement = Zero} 

machineList :: [Turing]
machineList = [weird3, almostweird3, fullsim_not_halt3, bb3, simple_sweeper, 
  checkerboardSweeper, goesLeftForever, binaryCounterTFTT, machineBreaksIndGuess]

instance Arbitrary Turing where 
  arbitrary = elements machineList 
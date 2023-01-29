{-# OPTIONS_GHC -Wno-orphans #-}
module TuringExamples where

import Relude
import qualified Relude.Unsafe as U
{-
examples of machines for induction
1) a completely vanilla binary counter
2) a 
-}

import Turing
import Count
import Skip
import Test.QuickCheck
import Notation
import Util
import Text.Parsec
import Parsing

--woah, this is a counting machine !!!
weird3 :: Turing
weird3 = unm "FL1FR0TL2TLHTR0TL2" 

counterIndHyp :: Config Count Bit 
-- 2 (F, n) >T< T F 
-- eg @ step 100
-- the thing we hope it goes to is
-- 0 (T, n) >T< T F 
-- eg @ step 170
counterIndHyp = Config (Phase 2) [(Bit False, symbolVarCount (SymbolVar 0) 1)] (Bit True) [(Bit True, One), (Bit False, One)]

counterIndHypReal :: Config Count Bit 
-- 2 F T (F, n) >T< T F 
-- eg @ step 100
-- the thing we hope it guesses is
-- 2 (F, n) >T< T F 
-- 0 (T, n) >T< T F 
-- eg @ step 170
--note that it needs to ignore the stuff that "doesn't matter"
counterIndHypReal = Config (Phase 2) [(Bit False, symbolVarCount (SymbolVar 0) 1), (Bit True, One), (Bit False, One)] (Bit True) [(Bit True, One), (Bit False, One)]

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

--writes TF one way then TT other way infinitely
checkerBoard2 :: Turing
checkerBoard2 = unm "TR1FL2TL1TR0___TL0"

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
-- p2 | (F, 1) >F< (T, x_0) (F, 1)
-- p2 | >F< (T, 1+ x_0) (F, 1) 

-- thingWhichShouldBeSelfGlued :: Skip Count Bit 
-- thingWhichShouldBeSelfGlued = Skip {_start = Config {_cstate = (Phase 2), _ls = [(Bit False,One)], _c_point = Bit False, _rs = [(Bit True,Count 0 (fromList []) (fromList [(BoundVar 0,Sum {getSum = 1})])),(Bit False,Count 1 (fromList []) (fromList []))]}, _end = EndMiddle (Config {_cstate = (Phase 2), _ls = [], _c_point = Bit False, _rs = [(Bit True,Count 1 (fromList []) (fromList [(BoundVar 0,Sum {getSum = 1})])),(Bit False,Count 1 (fromList []) (fromList []))]}), _hops = Count 0 (fromList []) (fromList [])} 

bb2 :: Turing
bb2 = unm "TL1TR1TR0TLH"

--steps left then right forever between state 0 and 1
loop2 :: Turing
loop2 = unm "FL1TLHFR0TLH"


jumps_to_end :: Turing
jumps_to_end = unm "TR1___FR1___"

--this was proven not to halt after a bit more time to simulate the OffToInfinityN proof
not_halt3 :: Turing
not_halt3 = unm "FL1TLHTR0FL2TR1TL0"

false_backward_search :: Turing
false_backward_search = unm "TR1___FR2_________"

--we got this machine from triggering the error in the second case statement in proveSimLinearAndTree
--haven't carefully analyzed it but from a quick look appears to be bin-counter-ish
{-
the bug went away when I changed there to be only one induction hypothesis. I think the problem is DFS
was using one of the indhyps first, and linear search was using the other one (somehow?) and so they 
were getting different answers, which does seem bad. But I definitely don't understand the problem 
as well as I could. 
-}
some_kind_of_bincounter :: Turing 
some_kind_of_bincounter = unm "TR1FL2FL0FR3TR3TL0FR1___"

--three machines that were on 16 Jan not proven by my program
{-
a slightly tricky christmas tree. it prints TTF forever, but while it just scans over it in one direction,
in the other direction it actually scoots it over one place. should be handled fine by k=3 multisymbol
-}
not_halt4a :: Turing 
not_halt4a = unm "TR1TL2FL2FR0TR1FL3TL0___"

{-
bog standard TF christmas tree 
-}
not_halt4b :: Turing 
not_halt4b = unm "TR1FL2FL2FR0TL0FL3TL0___"

{-
TF / TT counter, should be handled by k=2 multisymbol
-}
not_halt4c :: Turing 
not_halt4c = unm "TR1TR0FL2FR0___FL3TL0TL2"

{-
identified on 27 Mar 22 via it causing an assert to fail
a slightly tricky christmas tree which satisfies the skip:
p1 (F, 2) (T, n)   >F< (F, 1) 
p1 (F, 1) (T, n+2) >F< 
but does so via "wiggling" across the tape - instead of just scanning 
straight accross the trues it has a 3 step (p0p0p1) process whereby it 
scoots a single false from one side of the block of trues to the other
-}
trickyChristmasTree :: Turing 
trickyChristmasTree = unm "TR1TR0TL2FL0___TL3FR0FL1"

{-
this is a rightward growing counting machine that counts in FF / FT 
(ie 6 is 011 = (FF)(FT)(FT)) and briefly sets everything to T when doing a reset
-}
lastSize3 :: Turing 
lastSize3 = unm "TR1___TL2TR0FR0FL2"

{-
takes O(n^2) time to increase the size of the tape by O(1)
outer loop: 
(T, n) >F<
TT (F, n-2) >F<
inner loop:
FF (T, n) >F<
F (T, n+1)>F<
and
TT F (T, n) >F<
(T, n+3) >F<
I discovered this machine when it made the "assert" in proveSimLinearAndTree fail; 
uncovering the bug where DFS and proveBySimulating were doing different things because
the sorting of skips was not unique - if two skips took the same number of steps, then
they could be sorted in either order. 
-}
bouncerInBouncer :: Turing
bouncerInBouncer = unm "TR1FL2FL0FR1TR0TR3TL0___"

{-
This machine is also from the assert in proveSimLinearAndTree failing, on macro size 4. 
The way it works is it is a binary counter where the larger digits are represented 
by larger blocks of Ts. It's something like, the nth digit is represented by 2^n + 1, 
which would give 2, 3, 5, 9, but the biggest digit is 2 bigger or something like that. 
and the spacing after digit n is 2^(n+1) - 1 I think. I am now pretty solidly sure that is
correct. 

the proof I have that this counter runs forever: 

A_n (beta_n in notebook)
3 (F, 2^n -1) >F< (F, 2^(n+1))
2 (T, 2^n+1) (F, 2^n) |>

k_n 
2 (F, 2^n) >T< (T, x) (F, 2^(n+1) - 1)
2 (T, 2^(n+1))(F, x+2^n) >|

Proving A_(n+1) uses A_n and k_n 
Proving k_(n+1) uses A_(n+1) and k_n

We would indguess
3 (F, x) >F< (F, 2x) (T, x+3) (F, 2x) 
3        >F< (F, 4x) (T, 2x+3)
which I think can be proven using A_n and k_n but I'm not going to check right now
-}
binaryCounterVariableWidth :: Turing
binaryCounterVariableWidth =  unm "TR1___FR2FR1TL2FL3TR0FL3"

{-
Posted on bbchallenge discord by tomtom2357
After some startup effects, applies this rule with x=4 the first time. 
3 (T, 5) F (T, 7) F (T, x)
3 (T, 5) F (T, 7) F (T, x+12)
-}
difficultBilateralBouncer :: Turing
difficultBilateralBouncer =  unm "TR1FL0FR2TR3TL0TL2FL2FR4___TR0"

unproven_size4_24jul :: [Turing]
unproven_size4_24jul = unm <$> ["TR1FR1TL2FL1TR0FL1______","TR1TL0FR2FR1TL2FR3___FR0","TR1TR0TL1TR2TR3TL2___FR0","TR1TL2FL2FR1TL3TL1TL0___","TR1___FL2TR0FL3FR1TR0TL2","TR1___TR2TL1FL1TR3FR0FR2","TR1TL2FL2FR1TL0FL3FL2___","TR1TL0FR2TL2TL0FL0______","TR1FL2TL2FR0TL0TL1______","TR1___TL2FR0TR3FL1TR0TR2"]

{-
noncounters: 1 2 
1 guesses the right thing and fails to prove
2 fails to guess at 1k but guesses right thing at 2k

0: base state: >FF< (FF, n) TF
    makes another TF and pushes it left until it ... 
    wait this is just a binary counter with 0->FF and 1->TF right...
1: lr bouncer-in-bouncer thing like machine 9 above, blocksize 2, no idea why unproven
2: growing bouncer-in-bouncer. block size ?? 4 ??
3: binary counter of some kind
4: a binary counter but around the head is T >F< F F (binary number here)

further analysis of 3: 
 16 | 1 F (T, 5) >F< F F F
 31 | 1 T (TF, 3) T T >F< 

 103 | 1 F (T, 9) >F< F F F
 126 | 1 T (TF, 5) T T >F<
so from 31 it behaves mostly like a binary counter where 0->TF 1->TT
but it has 
  1 FT (TT, x) >FF< FF F
  1 T (TF, x+1) TT >FF< 
which has, notice, that "realignment" problem, in addition to being a 
plan to count from X111 to X00001
-}
unproven_size4_13sep :: [Turing] 
unproven_size4_13sep = unm <$> ["TR1___TL2FL3FR0FL2TR0TR3", "TR1FL2FL0TR0TL0FR3TR2___", "TR1___FR2FR1TL2FL3TL0FR3", "TR1TL0FL0TR2FR3FR1TR0___", "TR1FR3TL2TR1FR3FL2TR0___"]

--discovered late at night 13sep22 via causing the program to crash
failsAssert :: Turing
failsAssert = unm "TR1FR3TR2___FL0TR0TL2TR3"

--brady 1983 machines
{-"ternary counter" 
base state: 2 >F< all the way left
after a "big reset" (215) main tape is (TF, x) FT
just before it is all FT
0 -> TF 1 -> FF 2 -> FT
so it's a ternary counter, but 2222 counts to 2000 instead of 1000
-}
ternaryCounter :: Turing
ternaryCounter = unm "TR1FL2TL0TR0FR0FL3___TL2"

{-"tail eating dragon" (fast growth)
base: 0 | >F< F (T, x?)
9 x =    2
24 x =   4
87 x =  10
390 x = 28
x -> 3x - 2 or (x + 1) -> (3x + 1) 
via a sub-state that looks like 
(TTT, n) (FTT) (TTT, m) >FFF<
and moves 1 from n to m repeatedly, 
while grabbing additional tape from the right, hence the "fast" growth

-}
tailEatingDragonFast :: Turing
tailEatingDragonFast = unm "TR1FR3TR2___FL0TR0TL2TR3"

{-"tail eating dragon" (slow growth)
-}
tailEatingDragonSlow :: Turing
tailEatingDragonSlow = unm "TR1TL0TR2FR3TL0___FL0TR3"


inSameAsOutFailure18Sep :: Turing
inSameAsOutFailure18Sep = unm "TR1___FR2FR1TL2FL3TR0FL3"

{-1RB1RD_1LC1LB_0RC0RD_---0RE_1LA1RE
selected randomly from BBChallenge oct 1 to test my bbchallenge parser
it's a translated bouncer
-}
bbChallengeExample :: Turing 
bbChallengeExample = unm "TR1TR3TL2TL1FR2FR3___FR4TL0TR4"


fromBBChallenge :: Text -> Turing 
fromBBChallenge = unsafeFromRight . parse (parseBBChallenge 5 <* eof) ""
{-
bounces chaotically left and right
due I believe to IijiI, has a CTL consisting of (11|01)* or something
-}
trickyCTLMachine :: Turing 
trickyCTLMachine = fromBBChallenge "1RB0RB_1LC1RA_0LA1LD_0LE0LC_1RA---"

hardUnilateralBouncer :: Turing 
hardUnilateralBouncer = fromBBChallenge "1RB0LA_0RC1RD_1LA1LC_0LC0RE_---1RA"

--from cosmo. bounces back and forth but in a difficult way
weirdBouncer :: Turing
weirdBouncer = fromBBChallenge "1RB0LE_0RC1LD_1LC0RB_0LA---_1LD1LA"

{-someone on the bb challenge discord went through and found a machine which hits each
different subroutine of skelet's program  -}
skelet_Incremental_formula :: Turing
skelet_Incremental_formula = fromBBChallenge "1LC0LB_---1LA_1RD1RD_1LB1RE_1LE1RC"
skelet_Closed_position :: Turing
skelet_Closed_position = fromBBChallenge "1LC0RD_---1RD_1RD0LA_1RA1RE_1LE1RB"
skelet_Closed_transition_modulo :: Turing
skelet_Closed_transition_modulo = fromBBChallenge "1LC1RB_---0RA_1RD0LD_1LA1RE_1LC1RD"
skelet_Collatz_like :: Turing
skelet_Collatz_like = fromBBChallenge "1LC1RA_---0RA_1RD0LA_1LC1RE_1RD0RB"
skelet_Single_exone :: Turing
skelet_Single_exone = fromBBChallenge "1LC0RA_---0LA_1RD1LE_1RE1RE_1LB0RD"
skelet_Spec1_exone :: Turing
skelet_Spec1_exone = fromBBChallenge "1LC0LC_---0RD_1RD1LA_0RB1RE_1LC0RD"
skelet_Self_tuning_exone :: Turing
skelet_Self_tuning_exone = fromBBChallenge "1LC0LB_---1LD_1RD1LD_0LA1RE_1LD0RE"
skelet_Huffman :: Turing
skelet_Huffman = fromBBChallenge "1LC1RE_---1LA_0RD0LD_1LB1RD_1LA0RA"
skelet_BL_1 :: Turing
skelet_BL_1 = fromBBChallenge "1LB---_0RC0LC_1LE0RD_1RC1RD_1RB0LA"
skelet_BL_2 :: Turing
skelet_BL_2 = fromBBChallenge "1LC0RE_0LE---_1LD0LB_1RA0LA_0RA1RE"

skelet_machines :: [Turing]
skelet_machines = [skelet_Incremental_formula, skelet_Closed_position, skelet_Closed_transition_modulo, skelet_Collatz_like, skelet_Single_exone, skelet_Spec1_exone, skelet_Self_tuning_exone, skelet_Huffman, skelet_BL_1, skelet_BL_2]

{-assert generated on oct4 of machines which were only proveable by 1 of the 2 lin recurrence methods
-}
linrecurdiff :: [Turing]
linrecurdiff = unm <$> ["TR1TL2TL1TL2TR3FL0TLHFR1", "TR1TL1TL1TL2TR3FL0TLHFR1", "TR1TLHTL1FR2FR1TL3TR2FL3", "TR1TLHTR2FL1FR3TL1TL3FR2", "TR1TLHTL2FR1FL3TR1TR3FL2", "TR1FL0FR2TLHTL2TL3FR0FL3", "TR1FL0FR2FL3TL0TR0TLHTL0", "TR1FL0FR2TLHTR3FL3TL0TR1", "TR1TLHFR2TL3TL3FL0TL1FL1", "TR1FL0FR2TLHFR3TL2TL3FL0", "TR1FR1FL2TR0TR0FR3TL1TLH"]

{-examples of machines for induction
1) a completely vanilla binary counter
  counts to the left. 
  iterates through ph 0 [binnum]>F<
2) a binary counter of symbol size 3
  counts to the left
  iterates through ph 1 [binnum]>F<T 
    where binnum is written with 0->FFF 1->TFF
  and as the carrying happens, all the TFFs get converted to TTTs
3) that fucked binary counter with weird symbols and a weird top symbol
   counts to the left
   iterates through ph 1 [binnum]>F<
     where 0->TT 1->TF
4) the binary counter of variable symbol width
   expands to the left and right
   iterates through ph 3 >F< [binnum] (eg 382)
     where 1 is mapped to 2, 3, 5, 9 ... (2^n + 1) Ts except the leading 1 is (2^n + 3) Ts
     and 0 is mapped to the same number of Fs
     and before the first digit is 2 Fs
     and after each digit is 1, 3, 7, ... (2^(n+1)) Fs 
     and in order to count up, it counts up recursively 
       eg at 1022 ?
       wait no, I think it only recursively counts in order to carry through the highest #
       but I am not 100% here. 
-}
{-
1) a completely vanilla binary counter
guessed indhyp:
Right: in 0 steps we turn
phase: 2  (F, 1) |>F<|(T, 0 + 1*x_0 ) (F, 1)
into:
phase: 2|>F<|(T, 1 + 1*x_0 ) (F, 1)

2) a binary counter of symbol size 3
guessed indhyp:
Right: in 0 steps we turn
phase: 3  (|FFF|, 1) |>|FTT|<|(|TTT|, 0 + 1*x_0 ) (|TTF|, 1)
into:
phase: 3|>|FTT|<|(|TTT|, 1 + 1*x_0 ) (|TTF|, 1)

3) that fucked binary counter with weird symbols and a weird top symbol
guessed indhyp:
Right: in 0 steps we turn
phase: 2  (|FF|, 1) (|TF|, 0 + 1*x_0 ) |>|TT|<|(|FF|, 1)
into:
phase: 2(|TF|, 1 + 1*x_0 ) |>|TT|<|(|FF|, 1)

4) the binary counter of variable symbol width
the thing we should guess is 
2 (F, x) (T, 2x) (F, x+2) >F< (F, 2x) 
2        (T, 4x) (F, 2x+2) >F<
but the problem is the guesser is not smart enough to generalize x -> 0 and 2x -> 0 in 
  the right way, which sort of makes sense. It needs a global view of the thing but is 
  trying to proceed elementwise
-}
{-
scaffold analysis (with drop 1)
1) f (cadg)^n baehf
   the right thing is a subset: it is the first a to the last a

  prefix  f cadg 
  suffix    cadg baehf 
  "be at left or right" gives the prefix fad  suffix ad baef
  "simplest sig" doesn't pick out a, and it picks b, which is not right, but everything other than b is the same simplicity

2) ecafg (intersperse cafg (D <> [m..1])) bafgafje
where 
D[n] = intersperseSE dikh (\i -> (di * i)) <$> [n..0]
ie
ecafg                                               dikh bafgafje
ecafg                             dikh di dikh cafg dikh bafgafje
ecafg dikh di dikh didi dikh cafg dikh di dikh cafg dikh bafgafje

ecafg dikh di dikh didi dikh dididi dikh cafg 
      dikh di dikh didi dikh cafg dikh di dikh cafg dikh bafgafje

   first a to last a works again, I believe

   prefix  e cafg dikh
   suffix    cafg dikh bafgafje
   
   "leftmost / rightmost" gives 
   prefix  e af di
   suffix    af di afafe

   "simplest sig" throws out di, which is correct, and everything else is same complexity 
   (ie, second simplest doesn't throw anything out)

3)  
igfv swdqot (X <> [1..m]) nbfvsmaljki
where 
X[n] = (\i -> x + hzy*i + ehzy rdqopu) <$> [0..(n-1)] <> ncfv swdqot
ie 
igfv swdqot                                                                                                                    x e hzy rdqopu ncfv swdqot nbfvsmaljki
igfv swdqot                                                                      x e hzy rdqopu x hzy e hzy rdqopu ncfv swdqot x e hzy rdqopu ncfv swdqot nbfvsmaljki
igfv swdqot x e hzy rdqopu x hzy e hzy rdqopu x hzy hzy e hzy rdqopu ncfv swdqot x e hzy rdqopu x hzy e hzy rdqopu ncfv swdqot x e hzy rdqopu ncfv swdqot nbfvsmaljki

I think first f to last f works?
     
    prefix  igfv swdqot x e hzy rdqopu
    suffix              x e hzy rdqopu ncfv swdqot nbfvsmaljki

    "leftmost/rightmost"  
    prefix  ifv swdqot e hzy rdqop 
    suffix             e hzy rdqop fv swdqot bfvsmaljki

    simplest does some work here too, I think, reducing to 
    second simplest
    prefix  ifv swt  
    suffix          swt bfvsmaljki
    most simple
    prefix  i
    suffix     bmaljki
    so second simplest does work, I think

4) ia (g * n) jadgj becfhki
first i to first g is my A_n above and first g to f is my k_n, I think. so I think it "roughly" works 
    
    prefix  ia g
    suffix     g jadgj becfhki

    it's less clear what to say about this one, because it requires a double induction
    but we can see what the above heuristics would do anyway
    
    leftmost/rightmost 
    prefix  i 
    suffix    cfi
    so this is pretty clearly wrong / unhelpful, because we need more points in the thing for the double induction basically

    simplest (not after L/R, independently, unlike above)
    second simplest filters out zero items
    most simple
    prefix  i 
    suffix     d becfhki
    this is sort of helpful, but not actually - it still filters too much

    todo: maybe try these heuristics again, this time with the "drop 2" alphabet rather than the "drop 1" alphabet, since "drop 2"
    first of all is more the "right thing" and second has way more letters and thus filtering is more relevant

sig analysis codes:
putText $ (\x -> x <> "\n") $ showP $ (fmap . fmap . fmap . fmap) (\(a,b,c,d,e) -> (a,b,c,d)) $  scaffoldV0 @Bit 400 (inductionExamples U.!! 0)
putText $ (\x -> x <> "\n") $ showP $ (fmap . fmap . fmap . fmap) (\(a,b,c,d,e) -> (a,b,c,d)) $  scaffoldV0 @(Vec 3 Bit) 400 (inductionExamples U.!! 1)
putText $ (\x -> x <> "\n") $ showP $ (fmap . fmap . fmap . fmap) (\(a,b,c,d,e) -> (a,b,c,d)) $  scaffoldV0 @(Vec 2 Bit) 400 (inductionExamples U.!! 2)
putText $ (\x -> x <> "\n") $ showP $ (fmap . fmap . fmap . fmap) (\(a,b,c,d,e) -> (a,b,c,d)) $ scaffoldV0 @(Bit) 500 (inductionExamples U.!! 3)
-}
{-
todo to develop induction algorithm
- gather an indhyp for each of these 4
    makeIndGuess 300 <$> machines
    to do this for 2) I had to write orderSignatures which uses the second heuristic 
    of it's good if the machine is close to the left or right of the tape among 
    signatures of the same complexity. 
    to do this for 4) I will have to somehow make it so the numbers are generalized globally
    rather than locally, but I haven't done this yet. 
- get >=4 indices at which said config occurs
    obtainMachineConfigs
- get the history traces in between said indices
- get the common sigs across a machine's history trace
    putText $ showP $ fmap toList $ fmap obtainSigsWhichOccur $ obtainHistorySlices @(Vec 3 Bit) 400 (inductionExamples U.!! 1)
- possible filters
  - simple 
  - occurs frequently
  - left-side / right-side heuristic
  - self-apply heuristic

- scaffold: putText $ (\x -> x <> "\n") $ showP $ (fmap . fmap . fmap . fmap) (\(a,b,c,d,e) -> (a,b,c,d)) $  scaffoldV0 @Bit 400 (inductionExamples U.!! 0)


- how to turn a scaffold into a set of proof goals: 
1) find the common prefixes and suffixes of the characters the traces contain
2) filter down to the points where the machine is at the furthest left or right it 
gets (RLE-wise)
3) for now, try all pairs of 1 thing from prefix & 1 thing from suffix
4) given a set of history pairs, generalize it similarly to guessWhatHappensNext 
5) attempt to prove it via induction
6) once at least 1 induction succeeds, go back to trying to prove the full runForever 
   without induction

this won't get everything, but it should get all the counters and plausibly other things
-}
inductionExamples :: [Turing]
inductionExamples = 
  [ weird3
  , unproven_size4_24jul U.!! 3
  , unproven_size4_24jul U.!! 4
  , binaryCounterVariableWidth
  ]

machinesWhichBreakIndGuess :: [Turing] 
machinesWhichBreakIndGuess = unm <$> [
  "TR1FL1TR2TR3TL0___FR1FR3",
  "TR1___TL2FR3FL3FL2TL0TL2",
  "TR1FL2FR2FR1TR3TR1TL0___",
  "TR1___FL2FR2TL0TL3FL2FL3",
  "TR1FR2FL2FL1TL3TL1TR0___",
  "TR1___TR2FR3FL3FL2TL0TL2",
  "TR1___TL2FR2TL0TL3FL2FL3",
  "TR1___TL1FR2TL0TL3FL2FL3"
  ] 
  
machineList :: [Turing]
machineList = [weird3, almostweird3, fullsim_not_halt3, bb3, simple_sweeper, 
  checkerboardSweeper, goesLeftForever, binaryCounterTFTT, machineBreaksIndGuess, 
  false_backward_search, not_halt3, jumps_to_end, loop2, bb2,
  some_kind_of_bincounter, bouncerInBouncer, binaryCounterVariableWidth, 
  difficultBilateralBouncer]

instance Arbitrary Turing where 
  arbitrary = elements machineList 

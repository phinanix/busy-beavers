module ShortNames where

import Relude hiding (mapMaybe, filter, (??))
import Control.Lens

import Util
import Turing
import ExpTape
import Skip
import Count
import Simulate (initSimState)
import SimulateTwoBit

f :: Bit
f = Bit False 

t :: Bit
t = Bit True

ph :: Int -> Phase
ph = Phase 

ff :: TwoBit
ff = TwoBit (Bit False) (Bit False)

ft :: TwoBit
ft = TwoBit (Bit False) (Bit True)

tt :: TwoBit
tt = TwoBit (Bit True) (Bit True)

c :: Natural -> Count
c = FinCount

ci :: Natural -> InfCount
ci = NotInfinity . FinCount 

bv :: Int -> Natural -> Count
bv x = boundVarCount (BoundVar x)

bvi :: Int -> Natural -> InfCount
bvi x = boundVarInfCount (BoundVar x)

skipEx2 :: Skip Count TwoBit
skipEx2 = Skip (Config (Phase 0) [(ft, c 2), (tt, bv 1 1)] ft [(ft, bv 0 1), (ff, bv 1 1)]) 
  (SkipStepped (Phase 0) (Middle (ExpTape [] ft []))) 
  (c 50)

tapeEx2 :: (Phase, ExpTape TwoBit InfCount)
tapeEx2 = (Phase 0, ExpTape [(ft, ci 2), (tt, bvi 0 1), (ff, ci 1)] 
                            ft [(ft, ci 1), (ff, ci 1 <> bvi 0 1)])    
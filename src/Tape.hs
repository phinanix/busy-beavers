module Tape where

import Relude
import Relude.Unsafe as Unsafe (init, last)
import Control.Lens

import Turing

data Tape = Tape
  { left :: [Bit]
  , point :: Bit
  , right :: [Bit]
  } deriving (Eq, Ord, Show, Generic)
instance NFData Tape


--this function should not accumulates zeros where they are redundant
--functions to move the point of the tape left and right
--returning nothing if the list ends
tapeLeft :: Tape -> Tape
--when we'd stack an false bit onto the implicitly infinite stack of False,
--drop it instead
tapeLeft (Tape [] False []) = Tape [] False []
tapeLeft (Tape (l : ls) False []) = Tape ls l []
tapeLeft (Tape [] h rs) = Tape [] False (h : rs)
tapeLeft (Tape (l : ls) h rs) = Tape ls l (h : rs)

tapeRight :: Tape -> Tape
--analagous to above
tapeRight (Tape [] False []) = Tape [] False []
tapeRight (Tape [] False (r : rs)) = Tape [] r rs
tapeRight (Tape ls h []) = Tape (h : ls) False []
tapeRight (Tape ls h (r : rs)) = Tape (h : ls) r rs

mirrorTape :: Tape -> Tape
mirrorTape (Tape ls h rs) =  Tape rs h ls

ones :: Tape -> Int
ones (Tape ls h rs) = length $ filter (==True) $ ls <> rs <> [h]

dispTape :: Tape -> Text
dispTape (Tape ls h rs) = dispBits (reverse ls) <> ">" <> dispBit h <> "<" <> dispBits rs where
  dispBits :: [Bit] -> Text
  dispBits [] = ""
  dispBits bits = mconcat ((\i -> dispBit i <> " ") <$> Unsafe.init bits)
    <> dispBit (Unsafe.last bits)

--the type of proofs that a TM will not halt
-- - HaltUnreachable means the Halt state is never transitioned to from the current state
--   and any states it transitions to
-- - Cycle means that the state reached after a number of steps and a greater number
--   of steps is identical
-- - OffToInfinitySimple means that after the given number of steps, the machine will
--   continue off in the given direction infintitely, never changing states
-- - OffToInfinityN means that after the given number of steps, the machine will
--   continue off in the given direction infinitely, in a short loop, which is checked
--   up to a specified bound N
data HaltProof
  = HaltUnreachable Phase
  | Cycle Steps Steps
  | OffToInfinityN Steps Dir
  deriving (Eq, Ord, Show, Generic)
instance NFData HaltProof

mirrorHaltProof :: HaltProof -> HaltProof
mirrorHaltProof (OffToInfinityN s d) = OffToInfinityN s $ mirrorDir d
--mirrorHaltProof (OffToInfinitySimple s d) = OffToInfinitySimple s $ mirrorDir d
mirrorHaltProof h = h

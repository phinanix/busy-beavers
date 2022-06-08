module Results where

import Relude
import Control.Lens
import Prettyprinter

import Util
import Turing
import Tape
import HaltProof
import Skip
import ExpTape
import Notation (dispTuring)

-- s is symbol and a is the type of tape 
data SimResult c s = Halted Steps (FinalTape c s) --this is steps taken and int is the total displacement
               | Continue Steps Phase (ExpTape s c) Int
               | ContinueForever (HaltProof s)
               --the reason this is still in, is that in proveByInd / induction in general 
               --the machine might get stuck and we don't know a better way to handle that
               --yet 
               | MachineStuckRes
               deriving (Eq, Ord, Show, Generic)
instance (NFData c, NFData s) => (NFData (SimResult c s))
--this doesn't work for some bizarre reason, it gives some big kind error :c
-- $(makePrisms ''SimResult)

newtype SwitchTape c s = Switch (ExpTape s c) deriving (Eq, Ord, Show)

-- data MysteryResult c = MHalted Steps (Mystery TapeSymbol (FinalTape c))
--                | MContinue Steps Phase (Mystery TapeSymbol (SwitchTape c)) Int
--                | MContinueForever (Mystery TapeSymbol HaltProof)
--                --the reason this is still in, is that in proveByInd / induction in general 
--                --the machine might get stuck and we don't know a better way to handle that
--                --yet 
--                | MMachineStuckRes
--                deriving (Eq, Ord, Show, Generic)

_Continue :: Prism' (SimResult c s) (Steps, Phase, ExpTape s c, Int)
_Continue = prism' (\(a,b,c,d) -> Continue a b c d) (\case
  Continue n ph a i -> Just (n, ph, a, i)
  _ -> Nothing
  )

_MachineStuckRes :: Prism' (SimResult s a) ()
_MachineStuckRes = prism' (const MachineStuckRes) (\case
  MachineStuckRes -> Just ()
  _ -> Nothing)

dispResult :: (Pretty s, Pretty c, Show s, Show c) => SimResult c s -> Doc ann
dispResult (Halted steps finalTape) = prettyText $ "After " <> show steps
  <> " steps, halted with tape: \n" <> dispFinalTape finalTape
dispResult (Continue steps phase tape disp) = prettyText $ "step: " <> showInt3Wide steps
  <> " disp: " <> show disp
  <> " state: " <> show phase
  <> " tape: " <> showP tape
dispResult (ContinueForever proof) = prettyText "the machine will go forever via: "
  <> dispHaltProof proof
dispResult MachineStuckRes = prettyText "the machine got stuck!"

--the results should be
--  how many machines halted
--    the longest running N machines
--    the most ones N machines
--  how many ran forever, with which kind of proof
--  how many ran out of time
--  and keep a certain number thereof
data Results c s = Results
  { _haltCount :: Int
    , _longestRun :: Maybe (Int, Turing, FinalTape c s)
    , _mostOnes :: Maybe (Int, Turing, FinalTape c s)
  , _provenForever :: Int
    , _haltUnreachable :: Int
    , _cycledCount :: Int
    , _infinityN :: Int
    , _backwardSearches :: Int
    , _backwardExamples :: [Turing]
    , _skipInfinity :: Int
    , _linRecur :: Int
  , _unproven :: Int
    , _unprovenExamples :: [(Turing, Steps, Phase, ExpTape s c)]
  } deriving (Show, Eq, Ord, Generic)
instance (NFData s, NFData c) => NFData (Results c s)

$(makeLenses ''Results)

instance (Eq s, Eq c) => AsEmpty (Results c s) where
  _Empty = only $ Results
    { _haltCount = 0
      , _longestRun = Nothing
      , _mostOnes = Nothing
    , _provenForever = 0
      , _haltUnreachable = 0
      , _cycledCount = 0
      , _infinityN = 0
      , _backwardSearches = 0
      , _backwardExamples = []
      , _skipInfinity = 0
      , _linRecur = 0
    , _unproven = 0
      , _unprovenExamples = []
    }
--number of unproven examples to keep, used also for backward Examples
keepNum :: Int
keepNum = 3

addResult :: (Tapeable (FinalTape c s)) => Turing -> SimResult c s -> Results c s -> Results c s
addResult turing (Halted steps tape) r =
  addHalter $ addLongest $ addOnesiest (ones tape) r where
    addLongest r = case r ^. longestRun of
      Nothing -> r & longestRun ?~ (steps, turing, tape)
      Just (longestSteps, _, _) -> if steps > longestSteps
        then r & longestRun ?~ (steps, turing, tape) else r
    addOnesiest ones r = case r ^. mostOnes of
      Nothing -> r & mostOnes ?~ (ones, turing, tape)
      Just (mostOneCount, _, _) -> if ones > mostOneCount
      then r & mostOnes ?~ (ones, turing, tape) else r
    addHalter = haltCount +~ 1
addResult turing (ContinueForever proof) r =
  r & provenForever +~ 1 & proof2lens proof +~ 1 & special proof where
    proof2lens (HaltUnreachable _) = haltUnreachable
    proof2lens (Cycle _ _) = cycledCount
    proof2lens (OffToInfinityN _ _) = infinityN
    proof2lens BackwardSearch = backwardSearches
    proof2lens (SkippedToInfinity _) = skipInfinity
    proof2lens (LinRecur _ _) = linRecur
    special BackwardSearch = --if r ^. backwardSearches > keepNum then id else
      backwardExamples %~ (:) turing
    special _ = id
addResult turing (Continue steps phase tape _disp) r =
  let r' = r & unproven +~ 1 in
  if r' ^. unproven > keepNum then r'
    else r' & unprovenExamples %~ ((:) (turing, steps, phase, tape))
addResult turing MachineStuckRes _r
  = error $ "machine: " <> dispTuring turing <> "got machinestuckres !"

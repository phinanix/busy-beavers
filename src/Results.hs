module Results where

import Relude
import Control.Lens

import Util
import Config
import Turing
import Tape
import HaltProof

data SimResult a = Halted Steps a
               | Continue Steps Phase a
               | ContinueForever HaltProof
               deriving (Eq, Ord, Show, Functor)

dispResult :: (a -> Text) -> SimResult a -> Text
dispResult dispTape (Halted steps tape) = "After " <> show steps
  <> " steps, halted with tape: \n" <> dispTape tape
dispResult dispTape (Continue steps phase tape) = "step: " <> showInt3Wide steps
  <> " state: " <> show phase
  <> " tape: " <> dispTape tape
dispResult _ (ContinueForever proof) = "the machine will go forever via: "
  <> dispHaltProof proof

--the results should be
--  how many machines halted
--    the longest running N machines
--    the most ones N machines
--  how many ran forever, with which kind of proof
--  how many ran out of time
--  and keep a certain number thereof
data Results a = Results
  { _haltCount :: Int
    , _longestRun :: Maybe (Int, Turing, a)
    , _mostOnes :: Maybe (Int, Turing, a)
  , _provenForever :: Int
    , _haltUnreachable :: Int
    , _cycledCount :: Int
    , _infinityN :: Int
    , _backwardSearches :: Int
    , _backwardExamples :: [Turing]
    , _skipInfinity :: Int
  , _unproven :: Int
    , _unprovenExamples :: [(Turing, Steps, Phase, a)]
  } deriving (Show, Eq, Ord, Generic, Functor)
instance NFData a => NFData (Results a)

$(makeLenses ''Results)

instance Eq a => AsEmpty (Results a) where
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
    , _unproven = 0
      , _unprovenExamples = []
    }
--number of unproven examples to keep, used also for backward Examples
keepNum :: Int
keepNum = 3

addResult :: (Tapeable a) => Turing -> SimResult a -> Results a -> Results a
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
    proof2lens (BackwardSearch) = backwardSearches
    proof2lens (SkippedToInfinity _ _) = skipInfinity
    special BackwardSearch = --if r ^. backwardSearches > keepNum then id else
      backwardExamples %~ ((:) turing)
    special _ = id
addResult turing (Continue steps phase tape) r =
  let r' = r & unproven +~ 1 in
  if r' ^. unproven > keepNum then r'
    else r' & unprovenExamples %~ ((:) (turing, steps, phase, tape))

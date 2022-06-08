module SimulateSkip where

import Relude hiding (mapMaybe, filter, (??))
import Control.Lens
import Data.Map.Monoidal (MonoidalMap(..))
import Data.List (maximumBy, foldl1)
import qualified Data.List.NonEmpty as NE ((<|))
import Data.Map.Strict (assocs, keysSet, unions)
import Witherable
import Prettyprinter
import Control.Exception
import Safe.Partial

import Util
import Turing

import ExpTape
import Skip
import Count
import HaltProof
import Results
import Simulate (initSimState)
import TapeSymbol

{-
Morning of 9 May 22
Dataflow of the output side of a skip
Inside the Skip, there is a SkipEnd
applySkip turns a Skip into a SkipResult
pickBestSkip turns a (Skip,SkipResult) pair into a PartialStepResult
skipStep pairs applySkip and pickBestSkip and also can return Unknown directly
 it is used in downstream applications

SkipEnd is a Phase and a partial/full Config 
SkipResult is a Phase, a full tape, and hop + displacement + read (HDR) information
PartialStepResult is a Unknown edge, a MachineStuck, a Halted configuration w HDR info, 
  or a normal configuration with HDR info
We at one point care about, in essence, whether a "skipresult" halts or not, but that info
  isn't actually stored in a SkipResult, so we use pairs of Skip, SkipResult, looking at 
  whether the Skip itself is storing halting or not

So this dataflow is essentially trying to support one main / happy path: 
  take a Skip & an ExpTape, match them up, return the new tape + some extra information
But several other things can happen: the edge can be undefined, the machine can halt 
(potentially in a place that doesn't nicely sort into macro symbols), or we can realize 
we have proven the machine runs forever. 

Right now SkipResult is in a confused place, because it essentially is trying to pretend
we're on the main path, but we might not actually be on the main path yet, so it doesn't
quite make sense. We also need to allow a skip to have a lot more ability to throw the 
exceptional paths "within" itself.

Therefore, the new datatypes and flow should be thus:
1) PartialStepResult is mostly right as is. It needs a new case for "we proved the machine
  runs forever by X means" (probably of type CurHopNumber -> HaltProof), and the halting 
  case needs to handle the fact that a machine might halt in the middle of a macro symbol.
2) SkipResult is probably just destroyed. 
3) SkipEnd will remain, and keep its current two cases, but needs to be substantially 
  generalized. Halting becomes an explicit case of SkipEnd (and the boolean y/n halt is 
  removed from Skip), which handles the fact that the tape might be in an improper state.
  UnknownEdge and ProvenForever become new cases. 
Data processing works like this:
1) we match the front half of the skip to the current tape as before, which as before
  produces the extra info of what the remaining bits of the tape look like. 
2) we directly combine that info with the SkipEnd to produce a PartialStepResult. 
3) we define an ordering on PartialStepResults that determines which ones are preferable:
  (forever / halt) > step > unknownedge, step ordered by how many steps. Any two of forever,
  halt and unknownedge are an assertionerror to have both of. I thought unknownedge was an
  error to have with step also, but it's actually not - you have both unknownedge and step 
  in the edge case where the unknownedge takes you more hops forward than the step. The 
  reason you prefer step in this case is to share the work of taking the hops that are 
  possible without defining the new edge before eventually being forced to define it 
  (though it is a bit hard to imagine this coming up and it might be worth making it error
  for now to see if it ever does). 
-}

--c is type of "count", s is type of "symbol"
--TODO: make displacement its own newtype; or maybe just roll 
-- all its uses into ReadShift, that probably works too
data PartialStepResult c s = Unknown Edge
                         --hops, finaltape, usedskip
                         | Stopped InfCount (FinalTape c s) (Skip Count s)
                         --hops, newphase, newtape, usedskip, maybe disp, maybe readshift
                         | Stepped InfCount Phase (ExpTape s c) (Skip Count s)
                              (Maybe Int) (Maybe ReadShift)
                         | NonhaltProven (HaltProof s)
                         | MachineStuck
                        deriving (Eq, Ord, Show, Generic)

--which of these newtypes your history is tracks whether the history is forwards (element 0 is the first thing that happend)
--or reverse (element 0 is the most recent thing that happened)
newtype TapeHist s c = TapeHist {_tapeHist :: [(Phase, ExpTape s c)]} deriving (Eq, Ord, Show, Generic, Functor)
newtype ReverseTapeHist s c = ReverseTapeHist {_reverseTapeHist :: [(Phase, ExpTape s c)]} deriving (Eq, Ord, Show, Generic, Functor)
newtype DispHist = DispHist {_dispHist :: [Int]} deriving (Eq, Ord, Show, Generic)
newtype ReverseDispHist = ReverseDispHist {_reverseDispHist :: [Int]} deriving (Eq, Ord, Show, Generic)
newtype ReadShiftHist = ReadShiftHist {_readShiftHist :: [ReadShift]} deriving (Eq, Ord, Show, Generic)
newtype ReverseReadShiftHist = ReverseReadShiftHist {_reverseReadShiftHist :: [ReadShift]} deriving (Eq, Ord, Show, Generic)

instance (NFData s, NFData c) => NFData (TapeHist s c)
instance (NFData s, NFData c) => NFData (ReverseTapeHist s c)
instance NFData DispHist
instance NFData ReverseDispHist
instance NFData ReadShiftHist
instance NFData ReverseReadShiftHist

instance Bifunctor TapeHist where
  bimap = bimapDefault

instance Bifoldable TapeHist where
  bifoldMap = bifoldMapDefault

instance Bitraversable TapeHist where
  bitraverse :: forall a b c d f. (Applicative f) => (a -> f c) -> (b -> f d) -> TapeHist a b -> f (TapeHist c d)
  bitraverse f g (TapeHist hist) = TapeHist <$> go where
    go :: f [(Phase, ExpTape c d)]
    go = traverse (traverse (bitraverse f g)) hist

getTapeHist :: TapeHist s c -> [(Phase, ExpTape s c)]
getTapeHist = _tapeHist

getReverseTapeHist :: ReverseTapeHist s c -> [(Phase, ExpTape s c)]
getReverseTapeHist = _reverseTapeHist

getDispHist :: DispHist -> [Int]
getDispHist = _dispHist

getReverseDispHist :: ReverseDispHist -> [Int]
getReverseDispHist = _reverseDispHist

getReverseReadShiftHist :: ReverseReadShiftHist -> [ReadShift]
getReverseReadShiftHist = _reverseReadShiftHist

getReadShiftHist :: ReadShiftHist -> [ReadShift]
getReadShiftHist = _readShiftHist

data SimState s = SimState
  { _s_phase :: Phase
  , _s_tape :: ExpTape s InfCount
  , _s_book :: SkipBook s
  , _s_steps :: Steps --the number of "small" / machine steps we have simulated. 
  -- a list of the skips used so far in order
  -- since it is the skips used in order, the index 0 one takes us from step 0 to step 1
  --the slice that takes you from step 5 to step 13 is index 5 to index 12 inclusive
  , _s_trace :: [Skip Count s]
   --a list of the (phase, tape)s seen so far in order
  , _s_reverse_history :: ReverseTapeHist s InfCount
    --a map of the (phase, tape)s seen so far to the step count at which they were seen 
  , _s_history_set :: Map (Phase, ExpTape s InfCount) Int
  , _s_counter :: Int --the number of times we have taken a "big step". guaranteed to take on all values between 0 and n
  --the total amount of leftward (negative) or rightward (positive) displacement we have done, starting from 0
  , _s_displacement :: Int
  , _s_reverse_disp_history :: ReverseDispHist
  , _s_reverse_readshift_history :: ReverseReadShiftHist
  } deriving (Eq, Ord, Show, Generic)
instance (NFData s) => NFData (SimState s)

instance (Pretty s) => Pretty (SkipOrigin s) where
  pretty Initial = "an initial skip"
  pretty (Glued first second) = "a skip resulting from gluing" <> line <> pretty first <> line
    <> "along with" <> pretty second
  pretty (Induction _book _i) = "a skip proved by induction"
  pretty (GlueStepRange first second) = "a skip resulting from glueing all skips used in the step range"
    <> show first <> " to " <> show second
  pretty InductionHypothesis = "a skip which is our current induction hypothesis"

--displacement is measured in the count of "s", not in the count of atomic symbols
-- data SkipResult s c = Skipped
--   { _hopsTaken :: InfCount
--   , _newPhase :: Phase
--   , _newTape :: ExpTape s c
--   , _resultingDisp :: Maybe Int 
--   , _resRS :: Maybe ReadShift
--   } deriving (Eq, Ord, Show, Generic)

$(makeLenses ''TapeHist)
$(makeLenses ''ReverseTapeHist)
$(makeLenses ''DispHist)
$(makeLenses ''ReverseDispHist)
$(makeLenses ''ReadShiftHist)
$(makeLenses ''ReverseReadShiftHist)
$(makeLenses ''SimState)
$(makePrisms ''PartialStepResult)
-- $(makeLenses ''SkipResult)

s_history :: Getter (SimState s) (TapeHist s InfCount)
s_history = to $ TapeHist . reverse . getReverseTapeHist . view s_reverse_history

s_disp_history :: Getter (SimState s) DispHist
s_disp_history = to $ DispHist . reverse . getReverseDispHist . view s_reverse_disp_history

s_readshift_history :: Getter (SimState s) ReadShiftHist
s_readshift_history = to $ ReadShiftHist . reverse
  . getReverseReadShiftHist . view s_reverse_readshift_history

--TODO: clean up the duplication that exists between this and other histories and 
--and so on
addToRRSH :: HasCallStack => Maybe ReadShift -> ReverseReadShiftHist -> ReverseReadShiftHist
addToRRSH maybeRS (ReverseReadShiftHist histList) = case maybeRS of
  Nothing -> error "rs not present"
  Just rs -> ReverseReadShiftHist (rs : histList)

-- resConfig :: Lens (SkipResult s c) (SkipResult t d) (Config c s) (Config d t)
-- resConfig = lens get set where
--   get skipRes = etToConfig (skipRes ^. newPhase) (skipRes ^. newTape)
--   set :: SkipResult s c -> Config d t -> SkipResult t d
--   set (Skipped hops _oldPh _oldTape oldDisp rs) config
--     = Skipped hops newPh newTape oldDisp rs
--     where
--       (newPh, newTape) = configToET config

-- instance (Pretty s) => Pretty (SkipResult s InfCount) where
--   pretty (Skipped hops phase tape disp _rs) = "took " <> pretty hops <> " disp " <> pretty disp <> " ending in:\n"
--     <> pretty phase <> " tape: " <> pretty tape

initExpTape :: s -> ExpTape s InfCount
initExpTape s = ExpTape [(s, Infinity)] s [(s, Infinity)]

-- dispSkipResult :: SkipResult Bit InfCount -> Text
-- dispSkipResult (Skipped c p tape disp _rs)
--   = "skipped to phase: " <> dispPhase p
--   <> " and tape " <> dispExpTape tape
--   <> " in " <> dispInfCount c

instance (Ord s, Pretty s) => Pretty (SkipBook s) where
  pretty book = let skipPile = unions book in
    foldMap (\(s, o) -> "the skip:" <> line <> pretty s <> line
            <> "which resulted from" <> line <> pretty o <> line <> line)
              $ assocs skipPile

--returns nothing if the skip is inapplicable, else returns the result
applySkip :: forall s. (Eq s, Pretty s, Partial) => Skip Count s -> (Phase, ExpTape s InfCount)
  -> Maybe (PartialStepResult InfCount s)
applySkip skip@(Skip s _ _) (p, tape)
  = guard (s^.cstate == p) >> either (const Nothing) Just
      (packageResult skip tape =<< runEquations (matchSkipTape skip tape))
  -- = Skipped
  --     (updateCountToInf boundVs hopCount)
  --     (getSkipEndPhase e)
  --     <$> getFinalET e (newLs, newRs)
  --     --TODO : un-just-ified Just (currently fixed by laziness)
  --     -- in other words, somtimes, there is an error inside the ReadShift / shift, 
  --     -- but we don't force the thunk on those calls because we don't care about 
  --     -- the result (actually, because there is no sensical result), without the 
  --     -- "Just", "Skipped" is strict so we force the error, but with the Just, 
  --     -- we lazily never force the error and so it is just discarded on the branch
  --     -- we don't care about 
  --     <*> pure (Just shift)
  --     <*> pure (Just $ ReadShift (-startLLen) startRLen shift)
packageResult :: forall s. (Eq s, Pretty s, Partial) => Skip Count s
  -> ExpTape s InfCount
  -> (Map BoundVar InfCount, ([(s, InfCount)], [(s, InfCount)]))
  -> Either Text (PartialStepResult InfCount s)
packageResult skip@(Skip s e hopCount) tape (boundVs, tapeSides@(newLs, newRs))
  = case e of
    SkipHalt tp -> Right $ Stopped
      (updateCountToInf boundVs hopCount)
      (FinalTape (newLs, newRs) $ first NotInfinity tp)
      skip
    SkipUnknownEdge e -> Right $ Unknown e
    SkipNonhaltProven hp -> Right $ NonhaltProven hp
    SkipStepped ph tp -> Stepped
      (updateCountToInf boundVs hopCount)
      ph
      <$> getFinalET tp tapeSides
      <*> pure skip
      <*> pure (Just shift)
      <*> pure (Just $ ReadShift (-startLLen) startRLen shift)
      where
      getFinalET :: Partial => TapePush Count s -> ([(s, InfCount)], [(s, InfCount)]) -> Either Text (ExpTape s InfCount)
      getFinalET (Middle (ExpTape ls p rs)) (remLs, remRs) = let
        ans = ExpTape
          (finalizeList ls `etApp` remLs)
          p
          (finalizeList rs `etApp` remRs)
        assertCond = etSatisfiesInvariant ans
        msg = "we were applying: " <> showP skip <> "\nto tape:\n" <> showP tape <> "\nresulting in:\n" <> showP ans
        in
          (if not assertCond then trace msg else id) assert assertCond (Right ans)
        --TODO, this can fail if you are trying to prove an induction on a finite span of tape
        -- you can also hit this if you try to shift one point to the left but there is a 
        --symbolvar on the tape there 
      getFinalET (Side L newRs) (remLs, remRs) = do
        (point, remremLs) <- getNewPoint remLs
        pure $ ExpTape remremLs point (finalizeList newRs `etApp` remRs)
      getFinalET (Side R newLs) (remLs, remRs) = do
        (point, remremRs) <- getNewPoint remRs
        pure $ ExpTape (finalizeList newLs `etApp` remLs) point remremRs

      shiftL = endLLen - startLLen
      shiftR = startRLen - endRLen
      shift = assert (let
        ans = shiftL == shiftR
        msg = ("failing assert: " <> show (shiftL, shiftR)
          <> "start" <> show (startLLen, startRLen)
          <> "end" <> show (endLLen, endRLen)
          <> "\nskip: " <> showP skip)
        in
        (if ans then id else trace msg) ans)
        shiftL
      (startLLen, startRLen) = configLens s
      (endLLen, endRLen) = tpLens tp
      configLens :: Config Count s -> (Int, Int)
      configLens (Config _ph ls _p rs) = (getLen ls, getLen rs)
      tapeLens :: ExpTape s Count -> (Int, Int)
      tapeLens (ExpTape ls _p rs) = (getLen ls, getLen rs)
      tpLens :: TapePush Count s -> (Int, Int)
      tpLens = \case
      --TODO (XX) are these -1s totally insane
        Side L ls -> (-1, getLen ls)
        Side R rs -> (getLen rs, -1)
        Middle con -> tapeLens con

      getLen :: [(s, Count)] -> Int
      getLen xs = sum $ (\(_s, c) -> infCountToInt $ updateCountToInf boundVs c) <$> xs

      -- updatePoint :: Map BoundVar InfCount -> (s, Location Count) -> (s, Location InfCount)
      -- updatePoint bs = (_2. _Side . _1 %~ updateCount bs)
      updateList :: Map BoundVar InfCount -> [(s, InfCount)] -> [(s, InfCount)]
      updateList bs = fmap $ fmap (updateInfCount bs)
      finalizeList :: [(s, Count)] -> [(s, InfCount)]
      finalizeList = invariantifyList . updateList boundVs . fmap (fmap NotInfinity)
      updateInfCount :: Map BoundVar InfCount -> InfCount -> InfCount
      updateInfCount _m Infinity = Infinity
      updateInfCount m (NotInfinity c) = updateCountToInf m c
--we want to be able to apply a skip of counts to an ExpTape _ Count but also a
--skip of counts to an ExpTape _ Nat
lookupSkips :: (Ord s) => (Phase, s) -> SkipBook s -> Set (Skip Count s)
lookupSkips (p, s) book = keysSet $ book ^. atE (p, s)


--if the machine halts, pick that one, else pick the one that goes farther
-- skipFarthest :: (Eq s, Eq c, Eq c')
--   => (Skip c s, SkipResult s c')
--   -> (Skip c s, SkipResult s c')
--   -> Ordering
-- skipFarthest a b | a == b = EQ
-- skipFarthest (Skip _ _ _ True, _)   _ = LT
-- skipFarthest _   (Skip _ _ _ True, _) = GT
-- skipFarthest (_, res1) (_, res2) = compare (res1 ^. hopsTaken) (res2 ^. hopsTaken)

--
skipPrecedence :: (Eq s) 
  => PartialStepResult InfCount s
  -> PartialStepResult InfCount s
  -> Ordering
skipPrecedence a b | a == b = EQ
skipPrecedence res1 res2 = case (res1, res2) of
  (NonhaltProven _, Stopped {}) -> error "can't both run forever and halt"
  (Stopped {}, NonhaltProven _) -> error "can't both run forever and halt"
  (MachineStuck, _) -> error "shouldn't be comparing a stuck"
  (_, MachineStuck) -> error "shouldn't be comparing a stuck"
  (NonhaltProven _, _) -> GT
  (_, NonhaltProven _) -> LT 
  (Stopped {}, _) -> GT
  (_, Stopped {}) -> LT
  (Stepped c _ _ _ _ _, Stepped d _ _ _ _ _) -> compare c d
  (Stepped {}, Unknown _) -> GT
  (Unknown _, Stepped {}) -> LT
  (Unknown e, Unknown f) -> compare e f

--simulates one step of a TM using a skip-book
skipStep :: (TapeSymbol s, Pretty s) => Turing -> SkipBook s -> Phase -> ExpTape s InfCount
  -> PartialStepResult InfCount s
skipStep (Turing _ trans) book ph tape@(ExpTape _ls p _rs) =
  let bit = getPoint p in
  case trans ^. at (ph, bit) of
    Nothing -> Unknown (ph, bit)
    Just _ -> let ans = pickBestSkip $ getSkipsWhichApply book ph tape
      in
        --trace ("ans was: " <> show ans)
        ans

getSkipsWhichApply :: (Ord s, Pretty s, Show s, HasCallStack)
  => SkipBook s
  -> Phase
  -> ExpTape s InfCount
  -> [(Skip Count s, PartialStepResult InfCount s)]
getSkipsWhichApply book p tape@(ExpTape _ls bit _rs)
  = let
      --just tries applying all the skips. I think this will be ok, but is probably
      --too expensive and should be reworked for efficiency later
      skips = lookupSkips (p, bit) book
      appliedSkips = mapMaybe (\s -> (s,) <$> applySkip s (p, tape)) $ toList skips
      msg = "tape: " <> showP tape <> "\nskips which applied:\n" <> show appliedSkips
      in --trace msg 
        appliedSkips

pickBestSkip :: (Eq s) => [(Skip Count s, PartialStepResult InfCount s)]
  -> PartialStepResult InfCount s
pickBestSkip = \case
  [] -> MachineStuck --TODO :: can we generate this message somewhere better?
  appliedSkips -> maximumBy skipPrecedence $ snd <$> appliedSkips
    -- in
    --   --trace ("hops: " <> showP hops <> " bestskip was:" <> showP bestSkip) $
    -- if bestSkip ^. halts then Stopped hops newT bestSkip newD rs
    --   else Stepped hops newP newT bestSkip newD rs


type SkipTape = ExpTape Bit InfCount

skipStateFromPhTape :: (TapeSymbol s) 
  => Turing -> Phase -> ExpTape s InfCount  -> SimState s
skipStateFromPhTape t ph tape = SimState ph tape (initBook t) 0 []
  (ReverseTapeHist [(ph, tape)]) (one ((Phase 0,tape), 0)) 0 0
  (ReverseDispHist [0]) (ReverseReadShiftHist [])

initSkipState :: (TapeSymbol s) => Turing -> SimState s
initSkipState t = skipStateFromPhTape t (Phase 0) (initExpTape blank)

simulateOneMachine :: Int -> Turing -> SimState Bit
  -> ([Skip Count Bit], Either Edge (SimResult InfCount Bit))
simulateOneMachine limit t = \case
  --SimState p tape _book steps@((>= limit) -> True) trace _hist _ _counter -> (trace, Right $ Continue steps p tape)
  state | state ^. s_steps >= limit -> (state ^. s_trace, Right $ Continue (state ^. s_steps) (state ^. s_phase) (state ^. s_tape) (state ^. s_displacement))
  SimState p tape book steps trace hist histSet counter disp dispHist rsHist -> case skipStep t book p tape of
    MachineStuck -> error "machinestuck"
    Unknown e -> (trace, Left e)
    --TODO: maybe we're supposed to put the nonhaltproving skip on the trace?
    NonhaltProven hp -> (trace, Right $ ContinueForever hp)
    Stopped c finalTape skip ->
      (skip : trace, Right $ Halted (steps + infCountToInt c) finalTape)
    Stepped c newP newTape skip newDisp rs -> case c of
      --TODO
      Infinity -> (skip : trace, Right $ ContinueForever (OffToInfinityN steps L)) --(SkippedToInfinity steps skip))
      c -> let newHist = hist & reverseTapeHist %~ ((p, tape) :)
               newHistSet = histSet & at (p, tape) ?~ steps
               newDispHist = dispHist & reverseDispHist %~ (disp :)
        in
        simulateOneMachine limit t $ SimState newP newTape book (steps + infCountToInt c) (skip : trace)
           newHist newHistSet counter (disp + fromJust newDisp) newDispHist (addToRRSH rs rsHist)

simulateOneTotalMachine :: Int -> Turing -> ([Skip Count Bit], SimResult InfCount Bit)
simulateOneTotalMachine limit machine = (^?! _Right) <$> simulateOneMachine limit machine (initSkipState machine)

updateBookBit :: Edge -> Turing -> SkipBook Bit -> SkipBook Bit
updateBookBit edge (Turing _ trans) book =
  let newSkips = initTransSkip edge (trans ^?! ix edge) in
    foldr addInitialSkipToBook book newSkips

--TODO: known bug: we currently output a number higher than we should for step count
-- simulateWithSkips :: Int -> Turing -> Results SkipTape
-- simulateWithSkips limit startMachine
--   = loop (startMachine, initSkipState startMachine) [] Empty where
--   loop :: (Turing, SimState) -> [(Turing, SimState)]
--     -> Results (ExpTape Bit InfCount) -> Results (ExpTape Bit InfCount)
--   loop (t, s@(SimState p tape book steps trace hist histSet counter)) todoList !rs = case simulateOneMachine limit t s of
--     (_trace, Right result) -> recurse todoList $ addResult t result rs
--     (_trace, Left e) -> recurse ((newState <$> branchOnEdge e t) <> todoList) rs where
--       --we need to add the new skips to the TM's book
--       newState :: Turing -> (Turing, SimState)
--       newState t = (t, SimState p tape (updateBook e t book) steps trace hist histSet counter)
--       -- updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
--       -- updateBook (Turing _ trans) book =
--       --   let newSkips = initTransSkip e (trans ^?! ix e) in
--       --     foldr addInitialSkipToBook book newSkips
--   recurse [] result = result
--   recurse (x : xs) result = loop x xs result

-- simulateOneTotalMachine :: Int -> Turing -> ([Skip Bit], SimResult (ExpTape Bit InfCount))
-- simulateOneTotalMachine limit machine
--   = loop machine $ (initSKipState machine) where
--   loop :: Turing -> SimState -> ([Skip Bit], SimResult (ExpTape Bit InfCount))
--   loop _t (SimState p tape _book steps@((>= limit) -> True) trace _hist _histSet _counter) = (trace, Continue steps p tape)
--   loop t (SimState p tape book steps trace hist histSet counter) = case skipStep t book p tape of
--     MachineStuck -> error "machinestuck"
--     Unknown _e -> (trace, Continue steps p tape)
--     Stopped c newTape _ -> (trace, Halted (steps + infCountToInt c) newTape)
--     Stepped c newP newTape skip -> if c == Infinity
--       then (skip : trace, ContinueForever $ SkippedToInfinity steps skip)
--       else loop t $ SimState newP newTape book (steps + infCountToInt c) (skip : trace) hist histSet counter



-- simulateOneMachineByGluing :: Int -> Turing -> SimState
--   -> ([Skip Bit], SkipBook Bit, Either Edge (SimResult SkipTape))
-- simulateOneMachineByGluing limit t = \case
--   SimState p tape book steps@((>= limit) -> True) trace _hist _histSet _counter -> (trace, book, Right $ Continue steps p tape)
--   SimState p tape book steps trace hist histSet counter -> case skipStep t book p tape of
--     MachineStuck -> error "machinestuck"
--     Unknown e -> (trace, book, Left e)
--     Stopped c newTape skip -> (skip : trace, book, Right $ Halted (steps + infCountToInt c) newTape)
--     Stepped c newP newTape skip -> case c of
--       Infinity -> (skip : trace, book, Right $ ContinueForever (SkippedToInfinity steps skip))
--       c -> simulateOneMachineByGluing limit t
--               $ SimState newP newTape newBook (steps + infCountToInt c) (skip : trace) hist histSet counter where
--         newBook = case trace of
--           [] -> book
--           prevSkip : _rest -> case glueSkips prevSkip skip of
--             Left err -> error $ "used two skips in a row but couldn't glue:\n"
--               <> "reason: " <> err <> "\n" <> show (pretty prevSkip)
--               <> "\nsecond skip\n" <> show (pretty skip)
--             Right gluedSkip -> addSkipToBook gluedSkip (Glued prevSkip skip) book

-- simulateByGluing :: Int -> Turing -> Results (ExpTape Bit InfCount)
-- simulateByGluing limit startMachine
--  = loop (startMachine, initSkipState startMachine) [] Empty  where
--   loop :: (Turing, SimState) -> [(Turing, SimState)] -> Results SkipTape -> Results SkipTape
--   loop (t, s@(SimState p tape book steps trace hist histSet counter)) todoList rs = case simulateOneMachineByGluing limit t s of
--     (_trace, _book, Right result) -> recurse todoList $ addResult t result rs
--     (_trace, _book, Left e) -> recurse ((newState <$> branchOnEdge e t) <> todoList) rs where
--       --we need to add the new skips to the TM's book
--       newState :: Turing -> (Turing, SimState)
--       newState t = (t, SimState p tape (updateBook t book) steps trace hist histSet counter)
--       updateBook :: Turing -> SkipBook Bit -> SkipBook Bit
--       updateBook (Turing _ trans) book =
--         let newSkips = initTransSkip e (trans ^?! ix e) in
--           foldr addInitialSkipToBook book newSkips
--   recurse [] result = result
--   recurse (x : xs) result = loop x xs result
weird3Goal :: Skip Count Bit
weird3Goal = Skip
    -- 0 F (T, n) >T< F goes to 
    -- 0 (T, n+1) >T< F
    (Config (Phase 0) [(Bit True, newBoundVar 0), (Bit False, finiteCount 1)] (Bit True) [(Bit False, finiteCount 1)])
    (SkipStepped  (Phase 0) $ Middle (ExpTape
        [(Bit True, finiteCount 1 <> newBoundVar 0)] (Bit True) [(Bit False, finiteCount 1)]))
    (finiteCount 0) --obviously this is fake for now 


module Util where

import Relude
import qualified Relude.Unsafe as U
import Data.Map.Monoidal ( MonoidalMap )
import qualified Data.Set as S

import Control.Lens
import Safe.Exact (takeExact, dropExact, splitAtExact)
import Safe.Partial
import Prettyprinter
import qualified Data.List.NonEmpty as NE
import Control.Exception
import qualified Data.Vector as V
import qualified Data.Vector.Algorithms.Intro as Intro

type MMap = MonoidalMap

(.:) :: (a -> b) -> (c -> d -> a) -> c -> d -> b
(.:) f g a b = f (g a b)


showInt3Wide :: Int -> Text
showInt3Wide i@((\i -> i < 10) -> True) = "  " <> show i
showInt3Wide i@((\i -> i < 100) -> True) = " " <> show i
showInt3Wide i = show i

bind :: Monad m => (a -> m b) -> m a -> m b
bind = (=<<)

mfailGuard :: (MonadFail m) => Bool -> String -> m ()
mfailGuard True = const $ pure ()
mfailGuard False = fail

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) = fmap . fmap
infixl 4 <$$>

(<$$$>) :: (Functor f, Functor g, Functor h) => (a -> b) -> f (g (h a)) -> f (g (h b))
(<$$$>) = fmap . fmap . fmap
infixl 4 <$$$>

(<**>) :: (Applicative f, Applicative g) => f (g (a -> b)) -> f (g a) -> f (g b)
(<**>) = liftA2 (liftA2 ($))

(<%>) :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
(<%>) = traverse
infixl 5 <%>

(<<) :: Applicative f => f b -> f a -> f b
ma << mb = do
  a <- ma
  mb
  pure a

fromJust :: Partial => Maybe a -> a
fromJust (Just a) = a
fromJust Nothing = error "unsafe"

unsafeFromLeft :: Partial => Either a b -> a
unsafeFromLeft (Left a) = a
unsafeFromLeft (Right _) = error "unsafe"

unsafeFromRight :: Partial => Either a b -> b
unsafeFromRight (Right a) = a
unsafeFromRight (Left _) = error "unsafe"

atE :: (AsEmpty (IxValue m), At m) => Index m -> Lens' m (IxValue m)
--the second iso is of type Iso' (Maybe (IxValue m)) (IxValue m)
atE i = at i . iso (fromMaybe Empty) Just

--taken from https://stackoverflow.com/questions/4597820/does-haskell-have-list-slices-i-e-python
-- TODO: Use Vector package?
--inclusive of the endpoints 
slice :: Partial => Int -> Int -> [a] -> [a]
slice from to xs = if from > to then error ("from: " <> show from <> " to: " <> show to) else
  takeExact (to - from + 1) (dropExact from xs)

allEqual :: (Eq s) => [s] -> Bool
allEqual [] = True
allEqual (x : xs) = all (== x) xs

list1AllEqual :: (Ord a) => NonEmpty a -> Bool
list1AllEqual (x :| rest) = all (== x) rest

showOnEval :: (Show b, Pretty b) => b -> b
showOnEval x = trace (showP x) x

putPretty :: (Pretty a) => a -> IO ()
putPretty = putText . show . pretty

neZipExact :: Partial => NonEmpty a -> NonEmpty b -> NonEmpty (a, b)
neZipExact as bs = assertMsg (length as == length bs)
  ("lengths differ: " <> showP (length as, length bs))
   $ NE.zip as bs

showP :: (Pretty a, IsString s) => a -> s
showP = show . pretty

failMsg :: Text -> Maybe a -> Either Text a
failMsg t = maybe (Left t) Right

guardMsg :: Bool -> Text -> Either Text ()
guardMsg b msg = if not b then Left msg else Right ()

instance (Pretty a, Pretty b) => Pretty (Either a b) where
    pretty = \case
      Left a -> "Left: " <> pretty a
      Right b -> "Right: " <> pretty b

myLength :: [a] -> Integer
myLength = myRecLength 0

myRecLength :: Integer -> [a] -> Integer
myRecLength counter = \case
  [] -> undefined  --trace (show counter) counter 
  (x : xs) -> undefined --trace (show counter) $ myRecLength (counter + 1) xs 

prettyText :: Text -> Doc ann
prettyText = pretty

ceilDiv :: Natural -> Natural -> Natural
ceilDiv x y = if x `mod` y == 0 then x `div` y else 1 + (x `div` y)

firstT :: (Bitraversable t, Applicative f) => (a -> f c) -> t a d -> f (t c d)
firstT f = bitraverse f pure

secondT :: (Bitraversable t, Applicative f) => (b -> f d) -> t c b -> f (t c d)
secondT = bitraverse pure

intersectFold :: (Ord a, Foldable t) => t (Set a) -> Set a
intersectFold t = go $ toList t where
  go [] = Empty
  go (x : xs) = foldr S.intersection x xs

third :: (a -> b) -> (x, y, a) -> (x, y, b)
third f (x, y, a) = (x, y, f a)

second3 :: (a -> b) -> (x, a, y) -> (x, b, y)
second3 f (x, a, y) = (x, f a, y)

(!!!) :: (Partial) => [a] -> Int -> a
(!!!) list i = assert (i < length list) $ case (!!?) list i of
   Nothing -> error ("index " <> show i <> " list length " <> show (length list))
   Just a -> a

assertMsg :: Partial => Bool -> Text -> a -> a
assertMsg cond msg out = if cond then out else error  msg

warnMsg :: Partial => Bool -> Text -> a -> a
warnMsg cond msg out = if cond then out else
  trace (toString $ "Warning:" <> msg) out

(/\)
    :: (Functor f)
    => ((a -> (a, a)) -> (c -> (a, c)))
    -- ^ Lens' c a
    -> ((b -> (b, b)) -> (c -> (b, c)))
    -- ^ Lens' c b
    -> (((a, b) -> f (a, b)) -> (c -> f c))
    -- ^ Lens' c (a, b)
(lens1 /\ lens2) f c0 =
    let (a, _) = lens1 (\a_ -> (a_, a_)) c0
        (b, _) = lens2 (\b_ -> (b_, b_)) c0
        fab = f (a, b)
    in fmap (\(a, b) ->
            let (_, c1) = lens1 (\a_ -> (a_, a)) c0
                (_, c2) = lens2 (\b_ -> (b_, b)) c1
            in c2
            ) fab

infixl 7 /\

--this function is not actually writeable 
combineTraversal :: --Traversal' s a -> Traversal' s b -> Traversal' s (a,b)
  forall f a b s. (Applicative f)
  => (forall g. Applicative g => (a -> g a) -> s -> g s)
  -> (forall h. Applicative h => (b -> h b) -> s -> h s)
  -> ((a,b) -> f (a,b)) -> s -> f s
combineTraversal ta tb = undefined where
  helper :: (Applicative f) => (a -> f a) -> (b -> f b) -> ((a,b) -> f (a, b))
  helper f g (a,b) = (,) <$> f a <*> g b
  invHelper :: (Applicative f) => ((a,b) -> f (a, b)) -> (a -> f a, b -> f b)
  invHelper fg = undefined --((), ())

--this is the unsafe lens that asserts the thing is there
ixListLens :: Int -> Lens' [s] s
ixListLens i = lens get set where
  get :: [s] -> s
  get = flip (U.!!) i
  set :: [s] -> s -> [s]
  set xs newX = case splitAtExact i xs of
    (pref, _oldX:suf) -> pref ++ (newX:suf)
    _ -> error ("length: " <> show (length xs) <> " index: " <> show i)

bitraverseBoth :: (Bitraversable p, Applicative f) => (a -> f b) -> p a a -> f (p b b)
bitraverseBoth f = bitraverse f f

neMConcat :: (Monoid m) => NonEmpty m -> m
neMConcat (m :| ms) = foldl' (<>) m ms

sortVector :: Ord a => V.Vector a -> V.Vector a
sortVector = V.modify Intro.sort

sortUniqueVector :: Ord a => V.Vector a -> V.Vector a
sortUniqueVector = V.uniq . sortVector

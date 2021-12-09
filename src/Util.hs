module Util where

import Relude
import Data.Map.Monoidal
import Control.Lens
import Safe.Exact (takeExact, dropExact)
import Safe.Partial
import Prettyprinter
import qualified Data.List.NonEmpty as NE 
import Control.Exception

type MMap = MonoidalMap

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

(<**>) :: (Applicative f, Applicative g) => f (g (a -> b)) -> f (g a) -> f (g b)
(<**>) = liftA2 (liftA2 ($))

(<%>) :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
(<%>) = traverse
infixl 5 <%>

fromJust :: Partial => Maybe a -> a 
fromJust (Just a) = a 
fromJust Nothing = error "unsafe"

fromLeft :: Partial => Either a b -> a 
fromLeft (Left a) = a 

fromRight :: Partial => Either a b -> b 
fromRight (Right b) = b 

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
slice :: Int -> Int -> [a] -> [a]
slice from to xs = takeExact (to - from + 1) (dropExact from xs)

allEqual :: (Eq s) => [s] -> Bool 
allEqual [] = True 
allEqual (x : xs) = all (== x) xs 

showOnEval :: (Show b, Pretty b) => b -> b
showOnEval x = trace (showP x) x 

putPretty :: (Pretty a) => a -> IO ()
putPretty = putText . show . pretty

neZipExact :: NonEmpty a -> NonEmpty b -> NonEmpty (a, b)
neZipExact as bs = assert (length as == length bs) $ NE.zip as bs

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

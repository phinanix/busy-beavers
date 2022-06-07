{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes #-}
module Mystery where 

import Relude hiding (show)
import Text.Show ( Show(show) ) 

--this is terrible and hacky as fuck, but I don't feel like fucking with GHC's incredibly
--stupid constraint solver right now
data Mystery (k :: Type -> Constraint) (f :: Type -> Type) where 
  Mystery :: (k a, Typeable (f a), Ord (f a)) => f a -> Mystery k f 

data MyMaybe a = MyNothing | MyJust a 

instance Show a => Show (MyMaybe a) where 
  show = \case 
    MyNothing -> "MyNothing"
    MyJust a -> "MyJust " <> show a 

-- instance (forall x. k x => Show x, forall x. Show x => Show (MyMaybe x)) 
--     => Show (Mystery k MyMaybe) where 
--   show (Mystery f) = show f

instance (forall x. Show x => Show (f x)) => Show (Mystery Show f) where 
  show (Mystery f) = "Mystery: " <> show f
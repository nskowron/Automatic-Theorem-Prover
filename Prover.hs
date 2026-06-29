{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module HList where

import Data.Kind
import Data.Void
import Data.Type.Equality (type (==))

data HList (l :: [Type]) where
    HNil  :: HList '[]
    HCons :: e -> HList l -> HList (e ': l)


type Impl a b = a -> b
type And a b = (a, b)
newtype PS a = PS a


class Searchable a where
    search :: Maybe a


class Provable a where
    prove :: Maybe a

instance (Searchable (HList '[] -> a)) => Provable a where
    prove = fmap ($ HNil) (search :: Maybe (HList '[] -> a))


instance Searchable (HList c -> ()) where
    search = Just $ const ()

instance Searchable (HList c -> Void) where
    search = Nothing

instance Searchable (HList (a ': c) -> b) => Searchable (HList c -> Impl a b) where
    search = fmap (\proof -> \ctxt -> \x -> proof (HCons x ctxt)) (search :: Maybe (HList (a ': c) -> b))

instance (Searchable (HList c -> a), Searchable (HList c -> b)) => Searchable (HList c -> And a b) where
    search = liftA2 (\p1 p2 -> \ctxt -> (p1 ctxt, p2 ctxt)) (search :: Maybe (HList c -> a)) (search :: Maybe (HList c -> b))

instance Iterable (HList c -> PS a) => Searchable (HList c -> PS a) where -- consider adding a Set layer
    search = iter :: Maybe (HList c -> PS a)



class Iterable a where
    iter :: Maybe a

instance Iterable (HList '[] -> s) where
    iter = Nothing

instance Iterable (HList (s ': ts) -> s) where
    iter = Just $ \(HCons c _) -> c

instance Iterable (HList ts -> s) => Iterable (HList (t ': ts) -> s) where
    iter = fmap (\found -> \(HCons c cs) -> found cs) (iter :: Maybe (HList ts -> s))

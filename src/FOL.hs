module FOL where

import Proposition

import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl))


-- === Quantifiers === --
data Forall a p where
    Forall :: (forall (x :: a). p x) -> Forall a p

data Exists a p where
    Exists :: forall a (x :: a) (p :: a -> Type). p x -> Exists a p


-- === Predicate === --
class Predicate (p :: a -> Type) where
    type Unwrapped p (x :: a)
    wrap :: Unwrapped p x -> p x
    unwrap :: p x -> Unwrapped p x
    mapWrap :: (Unwrapped p x -> Unwrapped p y) -> (p x -> p y)

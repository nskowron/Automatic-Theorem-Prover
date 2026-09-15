module FOL where

import Proposition

import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl))
import Data.Type.Nat (Nat(..))


-- === Quantifiers === --
type Forall (x :: a) (p :: a -> Type) = Proxy x -> p x
type Exists x p = (x, p)


-- === Predicate === --
class Predicate (p :: a -> Type) where
    type Unwrapped p (x :: a)
    wrap :: Unwrapped p x -> p x
    mapWrap :: (Unwrapped p x -> Unwrapped p y) -> (p x -> p y)


-- === Experiments === --
type family n + m where
    Z + m = m
    (S n) + m = S (n + m)

type family n :*: m where
    Z :*: m = Z
    (S n) :*: m = m + (n :*: m)

class Inducible (n :: Nat) where
    induction
        :: f Z
        -> (forall m. f m -> f (S m))
        -> f n

instance Inducible Z where
    induction base _ = base

instance
    ( Inducible n
    ) => Inducible (S n) where
    induction base step = step (induction base step)

-- p :: Forall (x :: Nat) (Z + x :~: x)
-- p _ = Refl

newtype PlusNZero x = PlusNZero (x + Z :~: x)

instance Predicate PlusNZero where
    type instance Unwrapped PlusNZero x = (x + Z :~: x)
    wrap = PlusNZero
    mapWrap f = \(PlusNZero x) -> PlusNZero (f x)

p1 :: Inducible x => Forall (x :: Nat) PlusNZero
p1 _ = induction (wrap Refl) (mapWrap (\Refl -> Refl))

-- p2 :: Forall (x :: Nat) ((Z :*: x) :~: Z)
-- p2 _ = Refl

-- p3 :: Forall (x :: Nat) ((x :*: Z) :~: Z)
-- p3 _ = induction Refl (\Refl -> Refl)

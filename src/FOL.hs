module FOL where

import Proposition

import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl))
import Data.Type.Nat (Nat(..))


-- === Quantifiers === --
type Forall (x :: a) (p :: a -> Type) = p x
type Exists x p = (x, p)


-- === Predicate === --
class Predicate (p :: a -> Type) where
    type Unwrapped p (x :: a)
    wrap :: Unwrapped p x -> p x
    unwrap :: p x -> Unwrapped p x
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



newtype PlusZeroN x = PlusZeroN (Z + x :~: x)

instance Predicate PlusZeroN where
    type instance Unwrapped PlusZeroN x = (Z + x :~: x)
    wrap = PlusZeroN
    unwrap (PlusZeroN x) = x
    mapWrap f = \(PlusZeroN x) -> PlusZeroN (f x)

p :: Forall (x :: Nat) PlusZeroN
p = wrap Refl

newtype PlusNZero x = PlusNZero (x + Z :~: x)

instance Predicate PlusNZero where
    type instance Unwrapped PlusNZero x = (x + Z :~: x)
    wrap = PlusNZero
    unwrap (PlusNZero x) = x
    mapWrap f = \(PlusNZero x) -> PlusNZero (f x)

p1 :: Inducible x => Forall (x :: Nat) PlusNZero
p1 = induction (wrap Refl) (mapWrap (\Refl -> Refl))

newtype TimesNZero x = TimesNZero (Z :*: x :~: Z)

instance Predicate TimesNZero where
    type instance Unwrapped TimesNZero x = (Z :*: x :~: Z)
    wrap = TimesNZero
    unwrap (TimesNZero x) = x
    mapWrap f = \(TimesNZero x) -> TimesNZero (f x)

p2 :: Forall (x :: Nat) TimesNZero
p2 = wrap Refl

-- p3 :: Forall (x :: Nat) ((x :*: Z) :~: Z)
-- p3 _ = induction Refl (\Refl -> Refl)

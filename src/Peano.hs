module Peano where

import FOL

import Data.Type.Nat ( Nat(..) )
import Data.Type.Equality ( (:~:)(..) )


-- === Arithmetics === --
type family (n :: Nat) :+: (m :: Nat) where
    Z :+: m = m
    (S n) :+: m = S (n :+: m)

type family (n :: Nat) :*: (m :: Nat) where
    Z :*: m = Z
    (S n) :*: m = m :+: (n :*: m)


-- === Prettier Equals === --
type family (n :: Nat) :=: (m :: Nat) where
    n :=: m = n :~: m


-- === Experiments === --

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



-- newtype PlusZeroN x = PlusZeroN (Z + x :~: x)

-- instance Predicate PlusZeroN where
--     type instance Unwrapped PlusZeroN x = (Z + x :~: x)
--     wrap = PlusZeroN
--     unwrap (PlusZeroN x) = x
--     mapWrap f = \(PlusZeroN x) -> PlusZeroN (f x)

newtype PlusZeroN x = PZN (Z :+: x :=: x)

p :: Forall Nat PlusZeroN
p = Forall (PZN Refl)

-- newtype PlusNZero x = PlusNZero (x + Z :~: x)

-- instance Predicate PlusNZero where
--     type instance Unwrapped PlusNZero x = (x + Z :~: x)
--     wrap = PlusNZero
--     unwrap (PlusNZero x) = x
--     mapWrap f = \(PlusNZero x) -> PlusNZero (f x)

-- p1 :: Inducible x => Forall (x :: Nat) PlusNZero
-- p1 = induction (wrap Refl) (mapWrap (\Refl -> Refl))

-- newtype TimesNZero x = TimesNZero (Z :*: x :~: Z)

-- instance Predicate TimesNZero where
--     type instance Unwrapped TimesNZero x = (Z :*: x :~: Z)
--     wrap = TimesNZero
--     unwrap (TimesNZero x) = x
--     mapWrap f = \(TimesNZero x) -> TimesNZero (f x)

-- p2 :: Forall (x :: Nat) TimesNZero
-- p2 = wrap Refl

-- p3 :: Forall (x :: Nat) ((x :*: Z) :~: Z)
-- p3 _ = induction Refl (\Refl -> Refl)

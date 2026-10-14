module FOL where

import Eval
import Utils
import Peano
import Proposition

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import Data.Type.Nat ( Nat(..) )
import GHC.TypeLits ( Symbol )


-- === Equals === --
type n :=: m = n :~: m


-- === Quantifiers === --
data Predicate p x v where
    Predicate :: Eval (Apply p x (Lit v)) -> Predicate p x v

data Forall x a (p :: Type) where
    Forall :: (forall (v :: a). Predicate p x v) -> Forall x a p

data Exists x a (p :: Type) where
    Exists :: forall x a (v :: a) p. Predicate p x v -> Exists x a p


-- === Variable === --
data Variable where
    Any :: Symbol -> Variable
    All :: Symbol -> Variable
    
data Lit a


-- === Apply === --
type family Apply p x (v :: Type) where

    Apply (a -> b) x v = Apply a x v -> Apply b x v
    Apply (a `And` b) x v = Apply a x v `And` Apply b x v
    Apply (a `Or` b) x v = Apply a x v `Or` Apply b x v

    Apply (a :=: b) x v = Apply a x v :=: Apply b x v
    Apply (Forall x b q) x v = Forall x b q -- allow variable shadowing
    Apply (Forall y b q) x v = Forall y b (Apply q x v)
    Apply (Exists x b q) x v = Exists x b q -- allow variable shadowing
    Apply (Exists y b q) x v = Exists y b (Apply q x v)

    Apply (a :+: b) x v = Apply a x v :+: Apply b x v
    Apply (a :*: b) x v = Apply a x v :*: Apply b x v

    Apply x x v = v
    Apply y x v = y

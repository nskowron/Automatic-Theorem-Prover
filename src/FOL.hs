module FOL where

import Utils
import Proposition

import Peano ( Nat, (:+:), (:*:) )
import qualified Peano ( Eval )

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import GHC.TypeLits ( Symbol )


-- === Var === --
data Var (x :: Symbol)


-- === Equals === --
type n :=: m = n :~: m


-- === Quantifiers === --
data Predicate p x v where
    Predicate :: Eval (Apply p (Var x) v) -> Predicate p x v

data Forall (x :: Symbol) (a :: d -> Type) (p :: Type) where
    Forall :: (forall (v :: d). Predicate p x (a v)) -> Forall x a p

data Exists (x :: Symbol) (a :: d -> Type) (p :: Type) where
    Exists :: forall d (x :: Symbol) (a :: d -> Type) (v :: d) (p :: Type). Predicate p x (a v) -> Exists x a p


-- === Apply === --
type family Apply p x v where

    Apply (a -> b) x v = Apply a x v -> Apply b x v
    Apply (a `And` b) x v = Apply a x v `And` Apply b x v
    Apply (a `Or` b) x v = Apply a x v `Or` Apply b x v

    Apply (a :=: b) x v = Apply a x v :=: Apply b x v

    Apply (Forall x b q) (Var x) v = Forall x b q -- allow variable shadowing
    Apply (Forall y b q) x v = Forall y b (Apply q x v)
    
    Apply (Exists x b q) (Var x) v = Exists x b q -- allow variable shadowing
    Apply (Exists y b q) x v = Exists y b (Apply q x v)

    Apply (a :+: b) x v = Apply a x v :+: Apply b x v
    Apply (a :*: b) x v = Apply a x v :*: Apply b x v

    Apply x x v = v
    Apply y x v = y


-- === Eval === --
type family Eval p where

    Eval (a -> b) = Eval a -> Eval b
    Eval (a `And` b) = Eval a `And` Eval b
    Eval (a `Or` b) = Eval a `Or` Eval b

    Eval (a :=: b) = Eval a :=: Eval b

    Eval (Forall x a p) = Forall x a (Eval p)
    Eval (Exists x a p) = Exists x a (Eval p)

    Eval (a :+: b) = Peano.Eval (a :+: b)
    Eval (a :*: b) = Peano.Eval (a :*: b)

    Eval p = p

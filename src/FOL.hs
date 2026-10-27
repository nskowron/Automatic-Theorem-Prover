module FOL where

import Utils
import Proposition

import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import qualified ACFp ( Eval )

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import GHC.TypeLits ( Symbol )


-- === Var === --
data Var (x :: Symbol)


-- === Equals === --
type n :=: m = n :~: m


-- === Quantifiers === --
data Predicate p x v where
    Predicate :: Eval (Apply p '[ '(x, v)]) -> Predicate p x v

data Forall (x :: Symbol) (a :: d -> Type) (p :: Type) where
    Forall :: (forall (v :: d). Predicate p x (a v)) -> Forall x a p

data Exists (x :: Symbol) (a :: d -> Type) (p :: Type) where
    Exists :: forall d (x :: Symbol) (a :: d -> Type) (v :: d) (p :: Type). Predicate p x (a v) -> Exists x a p


-- === Apply === --
type family Apply p env where

    Apply (a -> b) env = Apply a env -> Apply b env
    Apply (a `And` b) env = Apply a env `And` Apply b env
    Apply (a `Or` b) env = Apply a env `Or` Apply b env

    Apply (a :=: b) env = Apply a env :=: Apply b env

    Apply (Forall x a p) env = Forall x a (Apply p ('(x, Var x) ': env))
    Apply (Exists x a p) env = Exists x a (Apply p ('(x, Var x) ': env))

    Apply (a :+: b) env = Apply a env :+: Apply b env
    Apply (a :-: b) env = Apply a env :-: Apply b env
    Apply (a :*: b) env = Apply a env :*: Apply b env
    Apply (a :/: b) env = Apply a env :/: Apply b env
    Apply (a :^: b) env = Apply a env :^: Apply b env

    Apply (Var x) env = LookUp x env

    Apply p env = p


-- === Replace === --
type family Replace p x y where

    Replace x x y = y

    Replace (a -> b) x y = Replace a x y -> Replace b x y
    Replace (a `And` b) x y = Replace a x y `And` Replace b x y
    Replace (a `Or` b) x y = Replace a x y `Or` Replace b x y

    Replace (a :=: b) x y = Replace a x y :=: Replace b x y

    Replace (Forall z a p) x y = Forall z a (Replace p x y)
    Replace (Exists z a p) x y = Exists z a (Replace p x y)

    Replace (a :+: b) x y = Replace a x y :+: Replace b x y
    Replace (a :-: b) x y = Replace a x y :-: Replace b x y
    Replace (a :*: b) x y = Replace a x y :*: Replace b x y
    Replace (a :/: b) x y = Replace a x y :/: Replace b x y
    Replace (a :^: b) x y = Replace a x y :^: Replace b x y

    Replace p x y = p


-- === Eval === --
type family Eval p where

    Eval (a -> b) = Eval a -> Eval b
    Eval (a `And` b) = Eval a `And` Eval b
    Eval (a `Or` b) = Eval a `Or` Eval b

    Eval (a :=: b) = Eval a :=: Eval b

    Eval (Forall x a p) = Forall x a (Eval p)
    Eval (Exists x a p) = Exists x a (Eval p)

    Eval p = ACFp.Eval p

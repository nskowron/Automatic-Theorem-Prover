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
data Forall (x :: Symbol) (p :: Type) where
    Forall :: p -> Forall x p

data Exists (x :: Symbol) (p :: Type) where
    Exists :: forall (t :: Type) (x :: Symbol) (p :: Type).
        Apply p (Var x) t -> Exists x p


-- === Apply === --
type family Apply p x y where

    Apply p x x = p
    Apply x x y = y

    Apply (a -> b) x y = Apply a x y -> Apply b x y
    Apply (a `And` b) x y = Apply a x y `And` Apply b x y
    Apply (a `Or` b) x y = Apply a x y `Or` Apply b x y

    Apply (a :=: b) x y = Apply a x y :=: Apply b x y

    Apply (Forall x p) (Var x) y = Forall x p -- allow variable shadowing
    Apply (Forall z p) x y = Forall z (Apply p x y)
    Apply (Exists x p) (Var x) y = Exists x p -- allow variable shadowing
    Apply (Exists z p) x y = Exists z (Apply p x y)

    Apply (a :+: b) x y = Apply a x y :+: Apply b x y
    Apply (a :-: b) x y = Apply a x y :-: Apply b x y
    Apply (a :*: b) x y = Apply a x y :*: Apply b x y
    Apply (a :/: b) x y = Apply a x y :/: Apply b x y
    Apply (a :^: b) x y = Apply a x y :^: Apply b x y

    Apply p x y = p

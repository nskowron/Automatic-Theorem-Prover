module FOL where

import Utils
import Proposition

import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import qualified ACFp ( Eval )

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import Data.Proxy ( Proxy(..) )
import GHC.TypeLits ( Symbol )


-- === Equals === --
type n :=: m = n :~: m


-- === Quantifiers === --
data Forall (x :: Type) (p :: Type) where
    Forall :: (forall t. Predicate p x t) -> Forall x p

data Exists (x :: Type) (p :: Type) where
    Exists :: forall t p x. Predicate p x t -> Exists x p


-- === Predicate === --
data Predicate (p :: Type) (x :: Type) (t :: Type) where
    Predicate :: Substitute p x t -> Predicate p x t


-- === Apply === --
type family Apply (p :: Type) (env :: [(Type, Type)]) where

    Apply (a -> b) env = Apply a env -> Apply b env
    Apply (a `And` b) env = Apply a env `And` Apply b env
    Apply (a `Or` b) env = Apply a env `Or` Apply b env

    Apply (a :=: b) env = Apply a env :=: Apply b env

    Apply (Predicate p x s) env = Predicate p x (Apply s env) -- allow variable shadowing
    Apply (Predicate p y s) env = Predicate (Apply p env) y (Apply s env)
    Apply (Forall x p) env = Forall x p -- allow tariable shadowing
    Apply (Forall y p) env = Forall y (Apply p env)
    Apply (Exists x p) env = Exists x p -- allow tariable shadowing
    Apply (Exists y p) env = Exists y (Apply p env)

    Apply x env = Get x env

type family ApplyList (ps :: [Type]) (env :: [(Type, Type)]) where

    ApplyList '[] env = '[]
    ApplyList (p ': ps) env = Apply p env ': ApplyList ps env


-- === Substitute === --
type family Substitute p x t where

    Substitute p x t = Apply p '[ '(x, t) ]

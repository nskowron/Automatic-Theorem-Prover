module SearchUtils where

import Utils
import Proposition
import FOL

import Data.Kind ( Type )
import Data.Type.Nat


-- === FV X === --
data X (n :: Nat)


-- === Config === --
data Config (context :: [Type]) (tabu :: [Type]) (free_variable :: Type)

type family GetContext config where
    GetContext (Config context _ _) = context

type family GetTabu config where
    GetTabu (Config _ tabu _) = tabu

type family GetFV config where
    GetFV (Config _ _ free_variable) = free_variable

type family GetNextFV config where
    GetNextFV (Config _ _ (X n)) = X (S n)

type family IncrementFV config where
    IncrementFV (Config context tabu (X n)) =
        Config context tabu (X (S n))

type family Assume a config where
    Assume a (Config context tabu free_variable) =
        Config (a ': context) tabu free_variable

type family Unassume a config where
    Unassume a (Config context tabu free_variable) =
        Config context (a ': tabu) free_variable


-- === Apply === --
type family Apply (p :: Type) (env :: [(Type, Type)]) where

    Apply (X n) env = Get (X n) env

    Apply (a -> b) env = Apply a env -> Apply b env
    Apply (a `And` b) env = Apply a env `And` Apply b env
    Apply (a `Or` b) env = Apply a env `Or` Apply b env

    Apply (a :=: b) env = Apply a env :=: Apply b env

    Apply (Predicate p x t) env = Predicate (Apply p ('(x, x) ': env)) x (Apply t env)
    Apply (Forall x a p) env = Forall x a (Apply p env)
    Apply (Exists x a p) env = Exists x a (Apply p env)

    Apply p env = p


-- === Utils === --
type family Map k e m where
    Map (X n) e m = m
    Map k e ('(x, k) ': m) = '(x, e) ': m
    Map k e ('(x, f) ': m) = '(x, f) ': Map k e m

-- type family Assume p c where
--     Assume True '[] = '[]
--     Assume p '[] = '[ '(p, Z) ]
--     Assume p ('(p, n) ': c) = '(p, S n) ': Assume True c
--     Assume p ('(q, n) ': c) = '(q, S n) ': Assume p c

-- type family Unassume p c where
--     Unassume p '[] = '[]
--     Unassume p ('(p, _) ': c) = Unassume p c
--     Unassume p ('(q, n) ': c) = '(Substitute q p True, n) ': Unassume p c

-- type family Premises c where
--     Premises '[] = '[]
--     Premises ('(p, _) ': c) = p ': Premises c

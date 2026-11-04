module AutomaticTests where

import Proposition
import ACFp
import FOL
import Prover

import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )


-- === Propositional Symbols === --
data A
data B
data C

-- === Propositional Logic === --
_ = prove @True
_ = prove @(True -> True)
_ = prove @(A -> True)
_ = prove @((A `Or` B) -> True)

_ = prove @(A -> A)
_ = prove @(A -> B -> A)

_ = prove @(A -> (A `And` A))
_ = prove @(A -> B -> (A `And` B))

_ = prove @((A `And` B) -> A)
_ = prove @((A `And` B) -> B)

_ = prove @((A `Or` A) -> A)
_ = prove @(A -> (A `Or` A))
_ = prove @(B -> (A `Or` B))
_ = prove @(A `Or` True)

_ = prove @(((A `And` B) -> C) -> (A -> B -> C))
_ = prove @((A -> B -> C) -> ((A `And` B) -> C))

_ = prove @((A -> B) -> (B -> C) -> (A -> C))
_ = prove @((A -> (B -> C)) -> (B -> (A -> C)))
_ = prove @((A -> B) -> (A -> C) -> (A -> (B `And` C)))

_ = prove @((A `And` B) -> (B `And` A))
_ = prove @((A `Or` B) -> (B `Or` A))

_ = prove @((A `And` (B `And` C)) -> ((A `And` B) `And` C))
_ = prove @((A `Or` (B `Or` C)) -> ((A `Or` B) `Or` C))
_ = prove @(A `And` (B `Or` C) -> ((A `And` B) `Or` (A `And` C)))
_ = prove @(((A `And` B) `Or` (A `And` C)) -> A `And` (B `Or` C))
_ = prove @(A `And` (A `Or` B) -> A)

_ = prove @(False -> A)
_ = prove @(False -> (A `And` B))
_ = prove @(False -> (A `Or` B))

_ = prove @((A `And` Not A) -> B)
_ = prove @(A -> (B -> Not A) -> B -> C)
_ = prove @(Not (A `And` False))

_ = prove @((A `Or` B) -> (A -> C) -> (B -> C) -> C)
_ = prove @((A -> C) -> (B -> C) -> (A `Or` B) -> C)


-- === First-Order Variables === --
data X
data Y
data Z

-- === First-Order Logic === --
_ = prove @(Forall X Var (X :=: X))

_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (X :=: X))))
_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (Y :=: Y))))
_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (Y :=: X))))
_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (X :=: Y))))

_ = prove @(Forall X Var (Forall Y Var (Forall Z Var (((X :=: Y) `And` (X :=: Z)) -> (Y :=: Z)))))
_ = prove @(Forall X Var (Forall Y Var (Forall Z Var (((X :=: Y) `And` (Z :=: X)) -> (Z :=: Y)))))
_ = prove @(Forall X Var (Forall Y Var (Forall Z Var (((X :=: Y) `And` (Y :=: Z)) -> (X :=: Z)))))

_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (Y :=: X) `And` (X :=: Y))))
_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (X :=: X) `And` (Y :=: Y))))

_ = prove @(Forall X Var (Forall Y Var (X :=: X)))
_ = prove @(Forall X Var (Forall Y Var (Forall X Var (X :=: X))))
_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> Forall Z Var (X :=: Y))))
_ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> Forall Z Var (Y :=: X))))

_ = prove @(Forall X Var (Forall Y Var (Forall Z Var (X :=: Z) -> (X :=: Y))))
_ = prove @(Forall X Var (Forall Y Var (Forall Z Var ((X :=: Z) -> (Z :=: X)) -> (X :=: Y))))

_ = prove @(Forall X Var (Exists Y Var (Y :=: X)))
_ = prove @(Forall X Var (Exists Y Var ((X :=: Y) `And` (Y :=: X))))
_ = prove @(Forall X Var (Exists Y Var ((X :=: X) `And` (Y :=: Y))))

_ = prove @(Exists X Var (X :=: X) -> Exists X Var (X :=: X))

_ = prove @(Forall X Var (Forall Y Var (Exists Z Var ((X :=: Z) `And` (Y :=: Z)) -> (X :=: Y))))
-- _ = prove @(Forall X Var (Exists Y Var (Forall Z Var ((X :=: Y) `And` (Y :=: Z)))) -> Forall X Var (Forall Y Var (X :=: Y)))


-- -- === First-Order Logic: Predicate-Free Theorems === --
-- _ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> (X :=: X) `And` (Y :=: Y))))
-- _ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> ((X :=: Y) `Or` (Y :=: X)))))
-- _ = prove @(Forall X Var (Forall Y Var (Not ((X :=: Y) `And` Not (X :=: Y)))))
-- _ = prove @(Forall X Var (Forall Y Var (((X :=: Y) `Or` Not (X :=: Y)))))
-- _ = prove @(Forall X Var (Forall Y Var (((X :=: Y) -> False) -> Not (X :=: Y))))
-- _ = prove @(Forall X Var (Forall Y Var (Not (X :=: Y) -> ((X :=: Y) -> False))))


-- -- === First-Order Logic: Equality Substitution === --
-- _ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> ((X :=: X) -> (Y :=: X)))))
-- _ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> ((Y :=: Y) -> (X :=: Y)))))
-- _ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> ((X :=: X) -> (Y :=: Y)))))
-- _ = prove @(Forall X Var (Forall Y Var ((X :=: Y) -> ((Y :=: Y) -> (X :=: X)))))
-- _ = prove @(Forall X Var (Forall Y Var (Forall Z Var ((X :=: Y) -> ((Y :=: Z) -> (X :=: Z))))))
-- _ = prove @(Forall X Var (Forall Y Var (Forall Z Var ((X :=: Y) -> ((Z :=: X) -> (Z :=: Y))))))

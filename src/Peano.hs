module Peano where

import qualified Data.Type.Nat as Nat ( Nat(..) )


-- === Domain === --
data Nat (n :: Nat.Nat)


-- === Declarations === --
data a :+: b
data a :*: b


-- === Eval === --
type family Eval p where

    Eval (Nat Nat.Z :+: b) = Eval b
    Eval (Nat (Nat.S a) :+: b) = Succ (Eval (a :+: b))

    Eval (Nat Nat.Z :*: b) = Nat Nat.Z
    Eval (Nat (Nat.S a) :*: b) = Eval (Eval (Nat a :*: b) :+: b)

-- helper --
type family Succ a where
    Succ (Nat a) = Nat (Nat.S a)

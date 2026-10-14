module Peano where

import Eval

import Data.Type.Nat ( Nat(..) )


-- === Declarations === --
data a :+: b
data a :*: b


-- === Definitions === --
type instance Eval (Z :+: b) = b
type instance Eval (S a :+: b) = S (Eval (a :+: b))

type instance Eval (Z :*: b) = Z
-- type instance Eval (S a :*: Z) = Eval (Eval (a :*: Z) :+: Z)

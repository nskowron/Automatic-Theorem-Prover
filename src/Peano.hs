module Peano where

-- import FOL

import Data.Type.Nat ( Nat(..) )
import Data.Type.Equality ( (:~:)(..) )


-- === Declarations === --
data a :+: b
data a :*: b


-- === Definitions === --
type family Eval p where

    Eval (Z :+: b) = b
    Eval (S a :+: b) = S (Eval (a :+: b))

    Eval (Z :*: b) = Z
    Eval (S a :*: b) = Eval (Eval (a :*: b) :+: b)

module ACFp where

import GHC.TypeLits


-- === Domain === --
data F (p :: Nat) (n :: Nat)


-- === Declarations === --
data a :+: b
data a :-: b
data a :*: b
data a :/: b
data a :^: b


-- === Eval === --
type family Eval p where

    Eval (F p a :+: F p b) = F p (Mod (a + b) p)
    Eval (F p a :-: F p b) = Eval (F p a :+: F p (p - Mod b p))
    Eval (F p a :*: F p b) = F p (Mod (a * b) p)
    Eval (F p a :/: F p b) = Eval (F p a :*: F p (Mod (b ^ (p - 1)) p))
    Eval (F p a :^: F p b) = F p (Mod (a ^ b) p)

    Eval p = p

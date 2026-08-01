module Examples where


import Proposition
import Prover

-- some propositional symbols for easy handling (TODO)
data A
data B
data C

-- define a proposition (a type)
type T1 = PS A -> PS B -> (PS A `And` PS B)

-- and try to prove it
p1 = prove @T1 -- p1 :: Maybe T1

-- for now i dont have a neat way of printing the proof 
-- object itself, but we can peek if a proof is successful
-- in interactive:

-- > printProof p1
-- "Proof Successful"

-- and now an unprovable one
type T2 = True -> (PS A -> PS B)
p2 = prove @T2

-- > printProof p2
-- "Nothing"
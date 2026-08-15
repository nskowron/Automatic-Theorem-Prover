module Examples where

import Proposition
import Prover


-- define a proposition (a type)
type T1 = (False -> True)

-- and try to prove it:
p1 = prove @T1 -- p1 :: T1

-- or prove a proposition directly:
p2 = prove @(A -> B -> (A `And` B))

-- p1 and p2 are objects of given types (proofs of given propositions)
-- but we don't have to load the proof to any object, we can just
-- check if it compiles (compiles <-> provable):
_ = prove @(A `Or` Not (B `And` Not B))

-- we can also instead emit the proof as a String
s3 = emit @((Not A `Or` Not B) -> Not (A `And` B))

-- then in interactive:
-------------------------------------------------------------------------------------
-- ghci> putStrLn s3
-- "\x1 -> \x2 -> case x1 of { Left x3 -> x3 $ fst $ x2; Right x3 -> x3 $ snd $ x2 }"
-------------------------------------------------------------------------------------

-- and now an unprovable one
type T3 = True -> (A -> B)
-- p3 = prove @T3

-- the above line should result in a compile error 
-- if uncommented:
-------------------------------------------------------------------------------------
-- No instance for ‘Inferable Unprovable '[] (True -> A -> B)’
-- [...]
-------------------------------------------------------------------------------------

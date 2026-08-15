module Provable where

import Proposition
import Prover


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

_ = prove @((A `Or` B) -> (A -> C) -> (B -> C) -> C)
_ = prove @((A -> C) -> (B -> C) -> (A `Or` B) -> C)
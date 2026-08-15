module Provable where

import Proposition
import Prover


data A
data B
data C

_ = prove @True
_ = prove @(True -> True)
_ = prove @(PS A -> True)
_ = prove @((PS A `Or` PS B) -> True)

_ = prove @(PS A -> PS A)
_ = prove @(PS A -> PS B -> PS A)

_ = prove @(PS A -> (PS A `And` PS A))
_ = prove @(PS A -> PS B -> (PS A `And` PS B))

_ = prove @((PS A `And` PS B) -> PS A)
_ = prove @((PS A `And` PS B) -> PS B)

_ = prove @((PS A `Or` PS A) -> PS A)
_ = prove @(PS A -> (PS A `Or` PS A))
_ = prove @(PS B -> (PS A `Or` PS B))
_ = prove @(PS A `Or` True)

_ = prove @(((PS A `And` PS B) -> PS C) -> (PS A -> PS B -> PS C))
_ = prove @((PS A -> PS B -> PS C) -> ((PS A `And` PS B) -> PS C))

_ = prove @((PS A -> PS B) -> (PS B -> PS C) -> (PS A -> PS C))
_ = prove @((PS A -> (PS B -> PS C)) -> (PS B -> (PS A -> PS C)))
_ = prove @((PS A -> PS B) -> (PS A -> PS C) -> (PS A -> (PS B `And` PS C)))

_ = prove @((PS A `And` PS B) -> (PS B `And` PS A))
_ = prove @((PS A `Or` PS B) -> (PS B `Or` PS A))

_ = prove @((PS A `And` (PS B `And` PS C)) -> ((PS A `And` PS B) `And` PS C))
_ = prove @((PS A `Or` (PS B `Or` PS C)) -> ((PS A `Or` PS B) `Or` PS C))
_ = prove @(PS A `And` (PS B `Or` PS C) -> ((PS A `And` PS B) `Or` (PS A `And` PS C)))
_ = prove @(((PS A `And` PS B) `Or` (PS A `And` PS C)) -> PS A `And` (PS B `Or` PS C))
_ = prove @(PS A `And` (PS A `Or` PS B) -> PS A)

_ = prove @(False -> PS A)
_ = prove @(False -> (PS A `And` PS B))
_ = prove @(False -> (PS A `Or` PS B))

_ = prove @((PS A `Or` PS B) -> (PS A -> PS C) -> (PS B -> PS C) -> PS C)
_ = prove @((PS A -> PS C) -> (PS B -> PS C) -> (PS A `Or` PS B) -> PS C)
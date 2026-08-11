module Provable where

import Proposition
import Prover


data A
data B
data C

t1 = prove @True
t2 = prove @(PS A -> True)
t3 = prove @(PS A -> PS A)
t4 = prove @(PS A -> PS B -> PS A)
t5 = prove @(PS A -> (PS A `And` PS A))
t6 = prove @(PS A -> PS B -> (PS A `And` PS B))
t7 = prove @((PS A `And` PS B) -> PS A)
t8 = prove @((PS A `And` PS B) -> PS B)
t9 = prove @(PS A -> (PS A `Or` PS A))
t10 = prove @((PS A `Or` PS B) -> True)
t11 = prove @(PS B -> (PS A `Or` PS B))
t12 = prove @(PS A `Or` True)
t13 = prove @(((PS A `And` PS B) -> PS C) -> (PS A -> PS B -> PS C))
t14 = prove @((PS A -> PS B -> PS C) -> ((PS A `And` PS B) -> PS C))
t15 = prove @((PS A -> PS B) -> (PS B -> PS C) -> (PS A -> PS C))
t16 = prove @((PS A -> (PS B -> PS C)) -> (PS B -> (PS A -> PS C)))
t17 = prove @((PS A -> PS B) -> (PS A -> PS C) -> (PS A -> (PS B `And` PS C)))
t18 = prove @((PS A `And` PS B) -> (PS B `And` PS A))
t19 = prove @((PS A `Or` PS B) -> (PS B `Or` PS A))
t20 = prove @((PS A `Or` PS A) -> PS A)
t21 = prove @((PS A `And` (PS B `And` PS C)) -> ((PS A `And` PS B) `And` PS C))
t22 = prove @((PS A `Or` (PS B `Or` PS C)) -> ((PS A `Or` PS B) `Or` PS C))
t23 = prove @(PS A `And` (PS B `Or` PS C) -> ((PS A `And` PS B) `Or` (PS A `And` PS C)))
t24 = prove @(((PS A `And` PS B) `Or` (PS A `And` PS C)) -> PS A `And` (PS B `Or` PS C))
t25 = prove @(PS A -> (PS A `Or` PS B))
t26 = prove @(PS A `And` (PS A `Or` PS B) -> PS A)
-- t27 = prove @(False -> PS A)
-- t28 = prove @(False -> (PS A `And` PS B))
-- t29 = prove @(False -> (PS A `Or` PS B))
t31 = prove @(PS A -> True)
t32 = prove @(True -> True)
t33 = prove @((PS A `Or` PS B) -> (PS A -> PS C) -> (PS B -> PS C) -> PS C)
t34 = prove @((PS A -> PS C) -> (PS B -> PS C) -> (PS A `Or` PS B) -> PS C)
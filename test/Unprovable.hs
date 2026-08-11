module Unprovable where

import Proposition
import Prover


data A
data B
data C

prove @False
prove @(PS A -> False)
prove @(PS A -> PS B)
prove @((PS A `Or` PS B) -> PS A)
prove @(PS A `Or` PS B -> PS A)
prove @(PS A `Or` PS B -> PS B)
prove @((PS A -> PS B) -> PS A)
prove @((PS A -> PS B) -> PS B)
prove @((PS A `And` PS B) -> PS C)
prove @(PS A -> PS B -> PS C)
prove @((PS A -> False) -> PS A)
prove @(PS A `Or` (PS A -> False))
prove @(((PS A -> False) -> False) -> PS A)
prove @(((PS A -> PS B) -> PS A) -> PS A)
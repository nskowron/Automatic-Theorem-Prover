module Tests where


import Proposition
import Prover

import Test.HUnit.Base


data A
data B
data C

--  helper for bool assertions
proofExists :: Maybe a -> Bool
proofExists (Just _) = True
proofExists Nothing = False

proofNotExists :: Maybe a -> Bool
proofNotExists = not . proofExists

runTests :: IO ()
runTests = do
    -- basics impl
    assertBool "T1"  $ proofExists    $ prove @True
    assertBool "T2"  $ proofNotExists $ prove @False
    assertBool "T3"  $ proofExists    $ prove @(PS A -> True)
    assertBool "T4"  $ proofNotExists $ prove @(PS A -> False)
    assertBool "T5"  $ proofExists    $ prove @(PS A -> PS A)
    assertBool "T6"  $ proofNotExists $ prove @(PS A -> PS B)
    assertBool "T7"  $ proofExists    $ prove @(PS A -> PS B -> PS A)

    -- and
    assertBool "T8"  $ proofExists    $ prove @(PS A -> (PS A `And` PS A))
    assertBool "T9"  $ proofExists    $ prove @(PS A -> PS B -> (PS A `And` PS B))
    assertBool "T10" $ proofExists    $ prove @((PS A `And` PS B) -> PS A)
    assertBool "T11" $ proofExists    $ prove @((PS A `And` PS B) -> PS B)

    -- or
    assertBool "T12" $ proofExists    $ prove @(PS A -> (PS A `Or` PS A))
    assertBool "T13" $ proofExists    $ prove @(PS B -> (PS A `Or` PS B))
    assertBool "T14" $ proofExists    $ prove @(PS A `Or` True)
    assertBool "T15" $ proofNotExists $ prove @((PS A `Or` PS B) -> PS A)

    -- curry & uncurry
    assertBool "T16" $ proofExists    $ prove @(((PS A `And` PS B) -> PS C) -> (PS A -> PS B -> PS C))
    assertBool "T17" $ proofExists    $ prove @((PS A -> PS B -> PS C) -> ((PS A `And` PS B) -> PS C))

    -- implication / composition
    assertBool "T18" $ proofExists    $ prove @((PS A -> PS B) -> (PS B -> PS C) -> (PS A -> PS C))
    assertBool "T19" $ proofExists    $ prove @((PS A -> (PS B -> PS C)) -> (PS B -> (PS A -> PS C)))

    -- and strengthening
    assertBool "T20" $ proofExists    $ prove @((PS A -> PS B) -> (PS A -> PS C) -> (PS A -> (PS B `And` PS C)))

    -- commutativity
    assertBool "T21" $ proofExists    $ prove @((PS A `And` PS B) -> (PS B `And` PS A))
    assertBool "T22" $ proofExists    $ prove @((PS A `Or` PS B) -> (PS B `Or` PS A)) -- DEBUG

    -- associativity
    assertBool "T23" $ proofExists    $ prove @((PS A `And` (PS B `And` PS C)) -> ((PS A `And` PS B) `And` PS C))
    assertBool "T24" $ proofExists    $ prove @((PS A `Or` (PS B `Or` PS C)) -> ((PS A `Or` PS B) `Or` PS C))

    -- distribution
    assertBool "T25" $ proofExists    $ prove @(PS A `And` (PS B `Or` PS C) -> ((PS A `And` PS B) `Or` (PS A `And` PS C)))
    assertBool "T26" $ proofExists    $ prove @(((PS A `And` PS B) `Or` (PS A `And` PS C)) -> PS A `And` (PS B `Or` PS C))

    -- absorption-ish
    assertBool "T27" $ proofExists    $ prove @(PS A -> (PS A `Or` PS B))
    assertBool "T28" $ proofExists    $ prove @(PS A `And` (PS A `Or` PS B) -> PS A)

    -- false / explosion
    assertBool "T29" $ proofExists    $ prove @(False -> PS A)
    assertBool "T30" $ proofExists    $ prove @(False -> (PS A `And` PS B))
    assertBool "T31" $ proofExists    $ prove @(False -> (PS A `Or` PS B))

    -- truth
    assertBool "T32" $ proofExists    $ prove @(PS A -> True)
    assertBool "T33" $ proofExists    $ prove @(True -> True)

    -- non-theorems (intuitionistic failures)
    assertBool "T34" $ proofNotExists $ prove @(PS A `Or` PS B -> PS A)
    assertBool "T35" $ proofNotExists $ prove @(PS A `Or` PS B -> PS B)
    assertBool "T36" $ proofNotExists $ prove @((PS A -> PS B) -> PS A)
    assertBool "T37" $ proofNotExists $ prove @((PS A -> PS B) -> PS B)
    assertBool "T38" $ proofNotExists $ prove @((PS A `And` PS B) -> PS C)
    assertBool "T39" $ proofNotExists $ prove @(PS A -> PS B -> PS C)
    assertBool "T40" $ proofNotExists $ prove @((PS A -> False) -> PS A)

    -- classical logic (should FAIL in intuitionistic system)
    assertBool "T41" $ proofNotExists $ prove @(PS A `Or` (PS A -> False))
    assertBool "T42" $ proofNotExists $ prove @(((PS A -> False) -> False) -> PS A)
    assertBool "T43" $ proofNotExists $ prove @(((PS A -> PS B) -> PS A) -> PS A)
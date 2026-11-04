# TODO

## Implementation

- [x] Move the Search Algorithm to compile time
  - [x] Elim False rule

- [x] Printing the Proof
  - [x] Think about changing Insert to :

- [ ] Extend the Provable Theory
  - [x] FOL
  - [ ] ACFp (optional)
    - [ ] add prime checking

- [ ] Using and Comparing Heuristics

## Refactor

- [x] README.md
  - [ ] Add a more detailed description
  - [x] Add an easier way of running the tests, cabal maybe?

- [ ] Organize source files

- [ ] Speed up (fix eagerness)
  - [ ] Replace :<|>:, :<$>:, :<*>: with type families with pattern matching

- [ ] The awkward display/emit
  - [ ] ShowNode with the '()
  - [ ] Add printing of goal conclusion type and intro var types

- [ ] Style unification
  - [ ] Unify kind expectations
  - [ ] Unify _
  - [ ] Unify exceptions for Try... rules

- [ ] Consider passing Find nodes to TryElimPremise

## Testing

- [ ] Make sure we don't lose computing ability because of the use of the Find flag
  - [ ] Generally prove correctness

- [ ] FOL tests

## Debugging

# TODO

## Implementation

- [x] Move the Search Algorithm to compile time
  - [x] Elim False rule
  - [ ] Think of passing the type into Project Node
    - can show (not infer) without passing the type
    - cannot even if we parametrized Node

- [x] Printing the Proof
  - [x] Think about changing Insert to :

- [ ] Extend the Provable Theory
  - [x] FOL
  - [ ] ACFp
    - [ ] add prime checking

- [ ] Using and Comparing Heuristics

## Refactor

- [x] README.md
  - [ ] Add a more detailed description
  - [x] Add an easier way of running the tests, cabal maybe?

- [ ] Organize source files

- [ ] The awkward display/emit
  - [ ] ShowNode with the '()
  - [ ] Add printing of goal conclusion type and intro var types

- [ ] Think about moving Apply like Eval

- [ ] unify kind expectations

## Testing

- [ ] Make sure we don't lose computing ability because of the use of the Find flag
  - [ ] Generally prove correctness

- [ ] FOL tests

## Debugging

# TODO

## Implementation

- [x] Move the Search Algorithm to compile time
  - [x] Elim False rule
  - [ ] Think of passing the type into Project Node
    - can show (not infer) without passing the type
    - cannot even if we parametrized Node

- [ ] Interactive Proving
  - [x] Using Monads
    - ivb style for now, non-interactive
  - [ ] Encode cursor movement as a function composition
  (that traverses the tree)

- [x] Printing the Proof
  - [x] Think about changing Insert to :

- [ ] Extend the Provable Theory
  - [x] FOL

- [ ] Using and Comparing Heuristics

## Refactor

- [x] README.md
  - [ ] Add a more detailed description
  - [x] Add an easier way of running the tests, cabal maybe?

- [ ] Organize source files
  - [ ] Move language extensions from Examples cabal into the file

- [ ] The awkward display/emit
  - [ ] ShowNode with the '()
  - [ ] Add printing of goal conclusion type and intro var types

- [ ] unwrap in induction node?

- [x] elim quantifier node naming change

- [x] parametrized node with forall?

- [x] rename WA to Predicate and pass to both quantifiers

- [ ] unify kind expectations

## Testing

- [ ] Make sure we don't lose computing ability because of the use of the Find flag
  - [ ] Generally prove correctness

- [ ] "Interactive" tests

- [ ] FOL tests

## Debugging

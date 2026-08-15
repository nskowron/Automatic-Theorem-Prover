# TODO

## Implementation

- [x] Move the Search Algorithm to compile time
  - [x] Elim False rule

- [ ] Interactive Proving
  - [ ] Using Monads

- [x] Printing the Proof
  - [x] Think about changing Insert to :

- [ ] Extend the Provable Theory

- [ ] Using and Comparing Heuristics

## Refactor

- [x] Order of imports
  - own: in the order of compilation
  - external: alphabetically

- [x] Order of constraints
  - in the order that they're needed

- [x] Move Insert to Utils

- [x] Replace Type with Proposition

- [x] Clean LANGUAGE pragmas
  - [x] Order of LANGUAGE pragmas
  - in cabal - alphabetically

- [x] Think about reducing info in elim nodes

- [x] Hardcore Refactor

- [x] Prettier error message?

- [x] README.md
  - [ ] Add a more detailed description
  - [x] Add an easier way of running the tests, cabal maybe?

- [x] Sort files more into different dirs

- [ ] The awkward display/emit

## Testing

- [x] Figure out compile-time tests

- [ ] Make sure we don't lose computing ability because of the use of the Find flag
  - [ ] Generally prove correctness

## Debugging

- [x] Fix wrong reduction order

- [x] Unprovable all with or in premise
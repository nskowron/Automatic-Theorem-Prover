# Automatic Theorem Prover

**Bachelor's Thesis — Automatic Theorem Prover in Haskell using the Curry–Howard correspondence.**

## Dependencies

### GHC and Cabal

To build and run the prover, you need:

* **[GHC](https://www.haskell.org/ghc/)** — the Glasgow Haskell Compiler
* **[Cabal](https://www.haskell.org/cabal/)** — Haskell's build system and package manager

The easiest way to install both is through **[GHCup](https://www.haskell.org/ghcup/)**.

### Libraries

Once Cabal is installed, run:

```bash
cabal install --lib HList
```

This downloads the [`Data.HList`](https://hackage.haskell.org/package/HList) package, which is currently the project's **only external dependency**.

## Project Structure

The [`automatic-theorem-prover.cabal`](automatic-theorem-prover.cabal) file defines the project's libraries and their dependencies.

The project currently contains **three libraries**:

### prover

This is the **main library** and the one you'll generally want to load with `cabal repl` when experimenting with the prover.

### test

More on project's tests [here](#tests).

### examples

Contains basic usage examples. See [`Examples.hs`](examples/Examples.hs).

## Compilation & Execution

### Build all libraries

From the project root:

```bash
cabal build
```

### Build a specific library

```bash
cabal build lib:<library>
```

For example:

```bash
cabal build lib:test
```

Don't be surprised if it takes a while - the prover proves in compile time.

### Open an interactive GHCi session

To compile and load a specific library into GHCi:

```bash
cabal repl lib:<library>
```

For example:

```bash
cabal repl lib:prover
```

This starts **GHCi** with everything set up and ready to import modules and experiment with the prover.

## Tests

Run the test suite with:

```bash
./runTests.sh
```

If the script doesn't have executable permissions yet, run:

```bash
chmod +x runTests.sh
```

## Project Description

*TODO*

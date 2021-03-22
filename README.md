# Lean SAT Proof Checker

This is an exploratory effort to build a proof checker for various formats
used by the SAT community.  Currently, we have focused on the [LRAT SAT Proof format](https://www.cs.utexas.edu/~marijn/publications/lrat.pdf).

## Building

To build the tool, you should follow the instructions in the
[Lean manual]() for installing Lean 4 including the `leanpkg` package
manager.  The main binary can then be built by running:

```
% leanpkg configure
% leanpkg build bin
```

This will put the binary in `./build/bin/SatChecker`.

## Checking a DIMACS file

To chec if a dimacs file is valid, you can use the `dimacs` command:

```
% ./build/bin/SatChecker dimacs <dimacsPath>
```

## Checking a lrat proof

To check a proof, use the `lrat` command:

```
% ./build/bin/SatChecker lrat <dimacsFile> <lratFile>
```

As an example, this checks one of the handcrafted proofs:

```
% ./build/bin/SatChecker lrat examples/handcrafted/lrat-fig1.dimacs examples/handcrafted/lrat-fig1.lrat
```
# Lean SAT Proof Checker

This is an exploratory effort to build a proof checker for various formats
used by the SAT community.  Currently, we have focused on the [LRAT SAT Proof format](https://www.cs.utexas.edu/~marijn/publications/lrat.pdf).

## Building

To build the tool, you should follow the instructions in the
[Lean manual](https://leanprover.github.io/lean4/doc/) for installing
Lean 4 including the `lake` build tool.
The main binary can then be built by running:

```shell
% lake build
```

This will put the binary in `./build/bin/sat-checker`.

## Checking a DIMACS file

To check if a dimacs file is valid, you can use the `dimacs` command:

```lean
% ./build/bin/sat-checker dimacs <dimacsPath>
```

## Checking a lrat proof

To check a proof, use the `lrat` command:

```lean
% ./build/bin/sat-checker lrat <dimacsFile> <lratFile>
```

As an example, this checks one of the handcrafted proofs:

```lean
% ./build/bin/sat-checker lrat examples/handcrafted/lrat-fig1.dimacs examples/handcrafted/lrat-fig1.lrat
```

# Lean SAT Proof Checker

This is an exploratory effort to build a proof checker for various formats
used by the SAT community.  Currently, we have focused on the [LRAT SAT Proof format](https://www.cs.utexas.edu/~marijn/publications/lrat.pdf).

To run the tool, you should follow the instructions in the
[Lean manual]() for installing Lean 4 including the `leanpkg` package
manager.  The main binary can then be built by running:

```
% leanpkg configure
% leanpkg build bin
```

Once the binary is built, you can then try it on example files by running:

```
% ./build/bin/LRat examples/handcrafted/lrat-fig1.dimacs examples/handcrafted/lrat-fig1.lrat
```
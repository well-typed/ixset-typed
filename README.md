
ixset-typed
===========

This Haskell package provides a data structure of sets that are indexed
by potentially multiple indices.

Sets can be created, modified, and queried in various ways.

The package is a variant of the [`ixset`][ixset] package. The `ixset` package
makes use of run-time type information to find a suitable index on a query,
resulting in possible run-time errors when no suitable index exists. In
`ixset-typed`, the types of all indices available or tracked in the type system.
Thus, `ixset-typed` should be safer to use than `ixset`, but in turn requires
more GHC extensions.

At the moment, the two packages are relatively compatible. As a consequence of
the more precise types, a few manual tweaks are necessary when switching from
one to the other, but the interface is mostly the same. The main other
differences are strictness behaviour, and the semantics of `getRange` and
similar interval selection operators (see the Haddocks).

  [ixset]: https://hackage.haskell.org/package/ixset


Benchmarks
----------

The package comes with a [`tasty-bench`][tasty-bench] benchmark suite. Every
benchmark is run at both `whnf` and `nf`, since an `IxSet` is spine-strict in
some places and lazy in others, so a change in the strictness of an operation
moves work between the two.  Timings are quite noisy but allocation figures are
more stable.

To check the effect of a change, record a baseline first and compare against
it (a regression can then be turned into a failure with `--fail-if-slower`):

    cabal bench --benchmark-options='--csv before.csv'
    ... apply patch ...
    cabal bench --benchmark-options='--baseline before.csv --csv after.csv'

  [tasty-bench]: https://hackage.haskell.org/package/tasty-bench

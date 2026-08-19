0.6 (2026-08-19)
================

* BREAKING CHANGE to the semantics of interval selection operators (`getRange`,
  `(@><)`, `(@>=<)`, `(@><=)`, `(@>=<=)`): if an index has multiple values, it
  will now be returned by interval selection only if a single value falls in the
  range (see [#3](https://github.com/well-typed/ixset-typed/issues/3)).
  Previously, these operators used two ordinal lookups and rebuilt the index in
  between, meaning that an element would be returned by `getRange` if one of its
  index values was greater than or equal to the lower bound and a different
  index value was below the upper bound.  If you still need the old behaviour,
  replace calls to these functions with the alternatives given in the Haddocks.

* Add various new API functions:

  - Lookup: `lookupIx`, `lookupIxMany`, `lookupOne`

  - Bulk modification: `insertSet`, `insertMany`, `deleteSet`, `deleteMany`, `deleteIxMany`

  - Set operations: `filter`, `difference`, `(\\\)`

  - Project out indices from values of an `Indexable` type: `project`

* Significant performance-related changes, including changes to
  strictness/laziness and removal of intermediate datastructures, which should
  generally improve performance, but may have performance downsides or lead to
  space leaks in some cases:

  - An `IxSet` is no longer always strict in the head of the `IxList`.  This
    means queries are more lazy, and avoid rebuilding the first index if it is
    not needed.  Updates continue to be strict, to prevent thunk leaks as the
    `IxSet` is updated.

  - `fromSet` and `fromList` now compute the indices lazily (but remain
    spine-strict in the elements).

  - The existing `union` and `intersection` set operations, and the new `filter`
    and `difference`, compute the indices lazily (waiting until the index is
    accessed, then it is computed in full).  Previously `union` and
    `intersection` would compute the indices partially (walking the index list
    strictly, but then using lazy `Map` operations).

* Add `forceIndices`, which can be used to ensure the indices are evaluated
  after using operations that are now lazy in the index construction.

* Generalise `@+` and `@*` so they work on any `Foldable` structure, not just lists.

* Various documentation and performance improvements.

* Rename `Data.IxSet.Typed.Ix` to `Data.IxSet.Typed.Internal.Ix`, change its API
  and add other `.Internal` modules.  These modules should not normally be
  needed and are subject to change.

* Remove various redundant constraints.

* Limit supported versions to GHC 9.2 and later.

* Drop dependency on `syb`.


0.5.1.1 (2026-07-13)
====================

* GHC 9.4 through to 9.14 compatibility.

0.5.1.0 (2022-05-10)
====================

* GHC 9.0 and 9.2 compatibility.

0.5 (2020-03-18)
================

* GHC 8.8 (and possibly 8.10) compatibility.

* safecopy-0.10 compatibility.

0.4.0.1 (2018-10-01)
====================

* containers-0.6 compatibility.

0.4 (2018-03-18)
================

* GHC 8.4 compatibility.

* Drop compatibility with GHC 7. GHC 8.4 introduces `Semigroup` as a superclass
  for monoid, and `Semigroup` is not in `base` prior to GHC 8. To avoid
  a conditional interface or a dependency on the `semigroups` package, we drop
  compatibility with GHC 7. There are not other changes in this version, so
  `ixset-typed-0.3.1.1` remains usable with GHC 7.

0.3.1.1 (2017-08-14)
====================

* GHC 8.2 compatibility.

0.3.1 (2016-06-21)
==================

* GHC 8.0 compatibility.

0.3 (2014-07-23)
================

* `IxSet` internals are now more strict

* The `empty` method of `Indexable` is now called `indices` and has a slightly
  different path; to migrate your code, if you were using Template Haskell,
  you probably do not have to change anything. Otherwise, wherever you have
  an instance of `Indexable` that looks like this

       instance Indexable MyIndexSet MyType where  -- OLD
         empty = mkEmpty ...

  change it to

       instance Indexable MyIndexSet MyType where  -- NEW
         indices = ixList ...


0.2 (2014-04-06)
================

* Add testsuite (which is a port of the ixset testsuite).

* Cleaning up and documentation.

* Add 'Foldable' and 'NFData' instances.


0.1.4 (2014-04-03)
==================

* Documentation.


0.1.3 (2014-04-02)
==================

* Export `IsIndexOf` class.


0.1.2 (2014-04-02)
==================

* Clean up export list.

* Documentation.


0.1.1 (2014-04-02)
==================

* Clean up export list.

* Documentation.


0.1.0.0 (2014-03-31)
====================

* Initial release.

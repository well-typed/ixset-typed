0.5.1.0 (2022-05-10)

- GHC 9.0.2 and 9.2.2 compatibility.

0.5 (2020-03-18)
================

- GHC 8.8 (and possibly 8.10) compatibility.

- safecopy-0.10 compatibility.

0.4.0.1 (2018-10-01)
====================

- containers-0.6 compatibility.

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

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

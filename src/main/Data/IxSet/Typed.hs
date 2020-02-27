{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{- |
An efficient implementation of queryable sets.

Assume you have a family of types such as:

> data Entry      = Entry Author [Author] Updated Id Content
>   deriving (Show, Eq, Ord)
> newtype Updated = Updated UTCTime
>   deriving (Show, Eq, Ord)
> newtype Id      = Id Int64
>   deriving (Show, Eq, Ord)
> newtype Content = Content String
>   deriving (Show, Eq, Ord)
> newtype Author  = Author Email
>   deriving (Show, Eq, Ord)
> type Email      = String
> data Test = Test
>   deriving (Show, Eq, Ord)

1. Decide what parts of your type you want indexed and make 'Indexed'
instances:

    > type EntryIxs = '[Author, Id, Updated, Test]
    > type IxEntry  = IxSet EntryIxs Entry
    >
    > instance Indexed Entry Author where
    >   ixFun (Entry a b _ _ _) = a : b
    >
    > instance Indexed Entry Id where
    >   ixFun (Entry _ _ _ i _) = [i]
    >
    > instance Indexed Entry Updated where
    >   ixFun (Entry _ _ u _ _) = [u]
    >
    > instance Indexed Entry Test where
    >   ixFun _ = []                    -- bogus index

2. Use 'insert', 'insertList', 'delete', 'updateIx', 'deleteIx'
and 'empty' to build up an 'IxSet' collection:

    > entries  = insertList [e1, e2, e3, e4] (empty :: IxEntry)
    > entries1 = foldr delete entries [e1, e3]
    > entries2 = updateIx (Id 4) e5 entries

3. Use the query functions below to grab data from it:

    > entries @= Author "john@doe.com" @< Updated t1

    Statement above will find all items in entries updated earlier than
    @t1@ by @john\@doe.com@.

4. Text index

    If you want to do add a text index create a calculated index.  Then if you want
    all entries with either @word1@ or @word2@, you change the instance
    to:

    > newtype Word = Word String
    >   deriving (Show, Eq, Ord)
    >
    > type EntryIxs = '[..., Word]
    > instance Indexed Entry Word where
    >     ixFun (Entry _ _ _ _ (Content s)) = map Word (words s)

    Now you can do this query to find entries with any of the words:

    > entries @+ [Word "word1", Word "word2"]

    And if you want all entries with both:

    > entries @* [Word "word1", Word "word2"]

5. Find only the first author

    If an @Entry@ has multiple authors and you want to be able to query on
    the first author only, define a @FirstAuthor@ datatype and create an
    index with this type.  Now you can do:

    > newtype FirstAuthor = FirstAuthor Email
    >   deriving (Show, Eq, Ord)
    >
    > type EntryIxs = '[..., FirstAuthor]
    > instance Indexed Entry FirstAuthor where
    >     ixFun (Entry author _ _ _ _) = [FirstAuthor author]

    > entries @= (FirstAuthor "john@doe.com")  -- guess what this does

-}

module Data.IxSet.Typed
    (
     -- * Set type
     IxSet(),
     IxList(),
     Indexable,
     IsIndexOf(),
     All,
     -- ** Declaring indices
     Ix(),
     Indexed(..),
     MkEmptyIxList(),

     -- ** Exceptions
     NotUniqueException(..),

     -- * Changes to set
     insert,
     insertList,
     delete,
     updateIx,
     updateUnique,
     deleteIx,
     deleteUnique,
     alterIx,
     filter,

     -- * Creation
     empty,
     fromSet,
     fromList,

     -- * Conversion
     toSet,
     toList,
     toAscList,
     toDescList,
     toFullDescList,
     getOne,
     getOneOr,
     getUnique,

     -- * Size checking
     size,
     null,

     -- * Set operations
     (&&&),
     (|||),
     union,
     intersection,
     difference,

     -- * Indexing
     (@=),
     (@<),
     (@>),
     (@<=),
     (@>=),
     (@><),
     (@>=<),
     (@><=),
     (@>=<=),
     (@+),
     (@*),
     getEQ,
     lookup,
     getLT,
     getGT,
     getLTE,
     getGTE,
     getRange,
     groupBy,
     groupAscBy,
     groupDescBy,
     groupFullDescBy,
     indexKeys,

     -- * Joins
     Joined(..),
     innerJoinUsing,

     -- * Debugging and optimization
     stats
)
where

import Prelude hiding (filter, null, lookup)

import Control.Arrow (first, second)
import Control.DeepSeq
import Control.Monad.Catch
import Data.Either
import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.IxSet.Typed.Ix (Ix (Ix))
import qualified Data.IxSet.Typed.Ix as Ix
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Lazy as MM
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid (mappend, mempty))
import Data.SafeCopy (SafeCopy (..), contain, safeGet, safePut)
import Data.Semigroup (Semigroup (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import GHC.Exts (Constraint)

--------------------------------------------------------------------------
-- The main 'IxSet' datatype.
--------------------------------------------------------------------------

-- | Set with associated indices.
--
-- The type-level list 'ixs' contains all types that are valid index keys.
-- The type 'a' is the type of elements in the indexed set.
--
-- On strictness: An 'IxSet' is "mostly" spine-strict. It is generally
-- spine-strict in the set itself. All operations on 'IxSet' with the
-- exception of queries are spine-strict in the indices as well. Query
-- operations, however, are lazy in the indices, so querying a number of
-- times and subsequently selecting the result will not unnecessarily
-- rebuild all indices.
--
data IxSet (ixs :: [*]) (a :: *) where
  IxSet :: !(Set a) -> !(IxList ixs a) -> IxSet ixs a

-- | An 'IxList' is a list of actual indices for an 'IxSet'. It is represented
-- as a list of maps of sets.
data IxList (ixs :: [*]) (a :: *) where
  Nil   :: IxList '[] a
  (:::) :: Ix ix a -> IxList ixs a -> IxList (ix ': ixs) a

infixr 5 :::

-- | A strict variant of ':::'.
(!:::) :: Ix ix a -> IxList ixs a -> IxList (ix ': ixs) a
(!:::) !ix !ixs = ix ::: ixs

infixr 5 !:::


--------------------------------------------------------------------------
-- Type-level tools for dealing with indexed sets.
--
-- These are partially internal. TODO: Move to different module?
--------------------------------------------------------------------------


-- | The constraint @All c xs@ says the @c@ has to hold for all
-- elements in the type-level list @xs@.
--
-- Example:
--
-- > All Ord '[Int, Char, Bool]
--
-- is equivalent to
--
-- > (Ord Int, Ord Char, Ord Bool)
--
type family All (c :: * -> Constraint) (xs :: [*]) :: Constraint
type instance All c '[]       = ()
type instance All c (x ': xs) = (c x, All c xs)

-- | 'Indexable' is a convenient shorthand for the instances that are necessary
-- to use 'IxSet'. If you want to use @'IxSet' ixs a@, you need
--
-- * An 'Ord' instance for @a@
-- * An 'Ord' instance for each @ix@ in @ixs@
-- * An 'Indexed' instance for @a@ and each @ix@ in @ixs@
type Indexable ixs a = (All Ord ixs, All (Indexed a) ixs, Ord a, MkEmptyIxList ixs)


-- | Operations related to the type-level list of index types.
class Ord ix => IsIndexOf (ix :: *) (ixs :: [*]) where

  -- | Provide access to the selected index in the list.
  access :: IxList ixs a -> Ix ix a

  -- | Map over the index list, treating the selected different
  -- from the rest.
  --
  -- The function 'mapAt' is lazy in the index list structure,
  -- because it is used by query operations.
  mapAt :: (All Ord ixs, All (Indexed a) ixs)
        => (Indexed a ix => Ix ix a -> Ix ix a)
              -- ^ what to do with the selected index
        -> (forall ix'. (Indexed a ix', Ord ix') => Ix ix' a -> Ix ix' a)
              -- ^ what to do with the other indices
        -> IxList ixs a -> IxList ixs a

instance
  {-# OVERLAPPING #-}
  Ord ix => IsIndexOf ix (ix ': ixs) where
  access (x ::: _xs)     = x
  mapAt fh ft (x ::: xs) = fh x ::: mapIxList ft xs

instance
  {-# OVERLAPPABLE #-}
  IsIndexOf ix ixs => IsIndexOf ix (ix' ': ixs) where
  access (_x ::: xs)     = access xs
  mapAt fh ft (x ::: xs) = ft x ::: mapAt fh ft xs

-- | Return the length of an index list.
--
-- TODO: Could be statically unrolled.
lengthIxList :: forall ixs a. IxList ixs a -> Int
lengthIxList = go 0
  where
    go :: forall ixs'. Int -> IxList ixs' a -> Int
    go !acc Nil        = acc
    go !acc (_ ::: xs) = go (acc + 1) xs

-- | Turn an index list into a normal list, given a function that
-- turns an arbitrary index into an element of a fixed type @r@.
ixListToList :: All Ord ixs
             => (forall ix. Ord ix => Ix ix a -> r)
                  -- ^ what to do with each index
             -> IxList ixs a -> [r]
ixListToList _ Nil        = []
ixListToList f (x ::: xs) = f x : ixListToList f xs

-- | Map over an index list.
mapIxList :: (All Ord ixs, All (Indexed a) ixs)
          => (forall ix. (Indexed a ix, Ord ix) => Ix ix a -> Ix ix a)
                -- ^ what to do with each index
          -> IxList ixs a -> IxList ixs a
mapIxList _ Nil        = Nil
mapIxList f (x ::: xs) = f x ::: mapIxList f xs

-- | Map over an index list (spine-strict).
mapIxList' :: (All Ord ixs, All (Indexed a) ixs)
           => (forall ix. (Indexed a ix, Ord ix) => Ix ix a -> Ix ix a)
                 -- ^ what to do with each index
           -> IxList ixs a -> IxList ixs a
mapIxList' _ Nil        = Nil
mapIxList' f (x ::: xs) = f x !::: mapIxList' f xs

-- | Zip two index lists of compatible type (spine-strict).
zipWithIxList' :: (All Ord ixs, All (Indexed a) ixs)
               => (forall ix. (Indexed a ix, Ord ix) => Ix ix a -> Ix ix a -> Ix ix a)
                    -- ^ how to combine two corresponding indices
               -> IxList ixs a -> IxList ixs a -> IxList ixs a
zipWithIxList' _ Nil        Nil        = Nil
zipWithIxList' f (x ::: xs) (y ::: ys) = f x y !::: zipWithIxList' f xs ys

--------------------------------------------------------------------------
-- Various instances for 'IxSet'
--------------------------------------------------------------------------

instance Indexable ixs a => Eq (IxSet ixs a) where
  IxSet a _ == IxSet b _ = a == b

instance Indexable ixs a => Ord (IxSet ixs a) where
  compare (IxSet a _) (IxSet b _) = compare a b

instance (Indexable ixs a, Show a) => Show (IxSet ixs a) where
  showsPrec prec = showsPrec prec . toSet

instance (Indexable ixs a, Read a) => Read (IxSet ixs a) where
  readsPrec n = map (first fromSet) . readsPrec n

instance (Typeable ixs, Typeable a, Indexable ixs a, SafeCopy a) => SafeCopy (IxSet ixs a) where
  putCopy = contain . safePut . toList
  getCopy = contain $ fmap fromList safeGet

instance (All NFData ixs, NFData a) => NFData (IxList ixs a) where
  rnf Nil        = ()
  rnf (x ::: xs) = rnf x `seq` rnf xs

instance (All NFData ixs, NFData a) => NFData (IxSet ixs a) where
  rnf (IxSet a ixs) = rnf a `seq` rnf ixs

instance Indexable ixs a => Semigroup (IxSet ixs a) where
  (<>) = mappend

instance Indexable ixs a => Monoid (IxSet ixs a) where
  mempty  = empty
  mappend = union

instance Foldable (IxSet ixs) where
  fold      = Fold.fold      . toSet
  foldMap f = Fold.foldMap f . toSet
  foldr f z = Fold.foldr f z . toSet
  foldl f z = Fold.foldl f z . toSet
  foldr' f z = Fold.foldr' f z . toSet
  foldl' f z = Fold.foldl' f z . toSet
  elem a    = Fold.elem a    . toSet -- Not recommended.
  minimum   = Fold.minimum   . toSet
  maximum   = Fold.maximum   . toSet
  sum       = Fold.sum       . toSet
  product   = Fold.product   . toSet
  length    = size
  toList    = toList
  null      = null

-- | Thrown when a function expecting a single unique value encounters
-- multiple values

data NotUniqueException = NotUnique
  deriving (Show)

instance Exception NotUniqueException

--------------------------------------------------------------------------
-- 'IxSet' construction
--------------------------------------------------------------------------

-- | An empty 'IxSet'.
empty :: Indexable ixs a => IxSet ixs a
empty = IxSet Set.empty mkEmptyIxList

-- | Create an empty 'IxList' which is part of an empty 'IxSet'. This class is
-- used internally because instances provide a way to do case analysis on a
-- type-level list. If you see an error message about this constraint not being
-- satisfied, make sure the @ixs@ argument to 'Indexable' is a type-level list.
class MkEmptyIxList (ixs :: [*]) where
  mkEmptyIxList :: IxList ixs a
instance MkEmptyIxList '[] where
  mkEmptyIxList = Nil
instance MkEmptyIxList ixs => MkEmptyIxList (ix ': ixs) where
  mkEmptyIxList = (Ix Map.empty) ::: mkEmptyIxList

-- | An 'Indexed' class asserts that it is possible to extract indices of type
-- @ix@ from a type @a@. Provided function should return a list of indices where
-- the value should be found. There are no predefined instances for 'Indexed'.
class Indexed a ix where
  ixFun :: a -> [ix]

--------------------------------------------------------------------------
-- Modification of 'IxSet's
--------------------------------------------------------------------------

type SetOp =
    forall a. Ord a => a -> Set a -> Set a

type IndexOp =
    forall k a. (Ord k,Ord a) => k -> a -> Map k (Set a) -> Map k (Set a)

-- | Higher order operator for modifying 'IxSet's.  Use this when your
-- final function should have the form @a -> 'IxSet' a -> 'IxSet' a@,
-- e.g. 'insert' or 'delete'.
change :: forall ixs a. Indexable ixs a
       => SetOp -> IndexOp -> a -> IxSet ixs a -> IxSet ixs a
change opS opI x (IxSet a indexes) = IxSet (opS x a) v
  where
    v :: IxList ixs a
    v = mapIxList' update indexes

    update :: forall ix. (Indexed a ix, Ord ix) => Ix ix a -> Ix ix a
    update (Ix index) = Ix index'
      where
        ds :: [ix]
        ds = ixFun x
        ii :: forall k. Ord k => Map k (Set a) -> k -> Map k (Set a)
        ii m dkey = opI dkey x m
        index' :: Map ix (Set a)
        index' = List.foldl' ii index ds
{-# INLINE change #-}

insertList :: forall ixs a. Indexable ixs a
           => [a] -> IxSet ixs a -> IxSet ixs a
insertList xs (IxSet a indexes) = IxSet (List.foldl' (\ b x -> Set.insert x b) a xs) v
  where
    v :: IxList ixs a
    v = mapIxList' update indexes

    update :: forall ix. (Indexed a ix, Ord ix) => Ix ix a -> Ix ix a
    update (Ix index) = Ix index'
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- xs, k <- ixFun x]

        index' :: Map ix (Set a)
        index' = Ix.insertList dss index

-- | Internal helper function that takes a partial index from one index
-- set and rebuilds the rest of the structure of the index set.
--
-- Slightly rewritten comment from original version regarding dss / index':
--
-- We try to be really clever here. The partialindex is a Map of Sets
-- from original index. We want to reuse it as much as possible. If there
-- was a guarantee that each element is present at at most one key we
-- could reuse originalindex as it is. But there can be more, so we need to
-- add remaining ones (in updateh). Anyway we try to reuse old structure and
-- keep new allocations low as much as possible.
fromMapOfSet :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
              => ix -> Set a -> IxSet ixs a
fromMapOfSet v a =
    IxSet a (mapAt updateh updatet mkEmptyIxList)
  where

    -- Update function for the index corresponding to partialindex.
    updateh :: Indexed a ix => Ix ix a -> Ix ix a
    updateh (Ix _) = Ix ix
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- Set.toList a, k <- ixFun x, k /= v ]

        ix :: Map ix (Set a)
        ix = Ix.insertList dss (Map.singleton v a)



    -- Update function for all other indices.
    updatet :: forall ix'. (Indexed a ix', Ord ix') => Ix ix' a -> Ix ix' a
    updatet (Ix _) = Ix ix
      where
        dss :: [(ix', a)]
        dss = [(k, x) | x <- Set.toList a, k <- ixFun x]

        ix :: Map ix' (Set a)
        ix = Ix.fromList dss


fromMapOfSets :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
              => Map ix (Set a) -> IxSet ixs a
fromMapOfSets partialindex =
    IxSet a (mapAt updateh updatet mkEmptyIxList)
  where
    a :: Set a
    a = nonEmptyFoldl (Map.elems partialindex)
    nonEmptyFoldl (i:xs) = List.foldl' Set.union i xs
    nonEmptyFoldl  [] = Set.empty


    -- Update function for the index corresponding to partialindex.
    updateh :: Indexed a ix => Ix ix a -> Ix ix a
    updateh (Ix _) = Ix ix
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- Set.toList a, k <- ixFun x, not (Map.member k partialindex)]

        ix :: Map ix (Set a)
        ix = Ix.insertList dss partialindex

    -- Update function for all other indices.
    updatet :: forall ix'. (Indexed a ix', Ord ix') => Ix ix' a -> Ix ix' a
    updatet (Ix _) = Ix ix
      where
        dss :: [(ix', a)]
        dss = [(k, x) | x <- Set.toList a, k <- ixFun x]

        ix :: Map ix' (Set a)
        ix = Ix.fromList dss

-- | Inserts an item into the 'IxSet'. If your data happens to have a primary
-- key this function is most likely /not/ what you want. In this case, use
-- 'updateIx' instead.
insert :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
insert = change Set.insert Ix.insert

-- | Removes an item from the 'IxSet'.
delete :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
delete = change Set.delete Ix.delete

-- | Internal implementation for update* family
updateIx' :: (Indexable ixs a, IsIndexOf ix ixs, MonadThrow m)
         => (IxSet ixs a -> m (Maybe a)) -> ix -> a -> IxSet ixs a -> m (IxSet ixs a)
updateIx' get i new ixset = do
  existing <- get $ ixset @= i
  pure $ insert new $
    maybe ixset (flip delete ixset) $
    existing

-- | Internal implementation for delete* family
deleteIx' :: (Indexable ixs a, IsIndexOf ix ixs, MonadThrow m)
         => (IxSet ixs a -> m (Maybe a)) -> ix -> IxSet ixs a -> m (IxSet ixs a)
deleteIx' get i ixset = do
  existing <- get $ ixset @= i
  pure $ maybe ixset (flip delete ixset) $
    existing

-- | Will replace the item with the given index of type 'ix'.
-- Only works if there is at most one item with that index in the 'IxSet'.
-- Will not change 'IxSet' if you have more than one item with given index.
updateIx :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> a -> IxSet ixs a -> IxSet ixs a
updateIx i new ixset = fromRight ixset $ updateIx' (Right . getOne) i new ixset


-- | Will replace the item with the given index of type 'ix'.
-- Only works if there is at most one item with that index in the 'IxSet'.
-- Will not change 'IxSet' if you have more than one item with given index.
alterIx :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> (Maybe a -> Maybe a)  -> IxSet ixs a -> (IxSet ixs a, (Maybe a, Maybe a))
alterIx i f ixset =
  let existing = lookup i ixset
      new = f existing
  in ((maybe id insert new) $
    maybe ixset (flip delete ixset) $
    existing,(existing,new))

-- | Will replace the item with the given index of type 'ix'.
-- Only works if there is at most one item with that index in the 'IxSet'.
-- Will throw if there is more than one item with given index.

-- Throws: 'NotUniqueException

updateUnique :: (Indexable ixs a, IsIndexOf ix ixs, MonadThrow m)
         => ix -> a -> IxSet ixs a -> m (IxSet ixs a)
updateUnique = updateIx' getUnique

-- | Will delete the item with the given index of type 'ix'.
-- Only works if there is at  most one item with that index in the 'IxSet'.
-- Will not change 'IxSet' if you have more than one item with given index.
deleteIx :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> IxSet ixs a -> IxSet ixs a
deleteIx i ixset = fromRight ixset $ deleteIx' (Right . getOne) i ixset

-- | Will delete the item with the given index of type 'ix'.
-- Only works if there is at  most one item with that index in the 'IxSet'.
-- Will throw if there is more than one item with given index.

-- Throws: 'NotUniqueException

deleteUnique :: (Indexable ixs a, IsIndexOf ix ixs, MonadThrow m)
         => ix -> IxSet ixs a -> m (IxSet ixs a)
deleteUnique = deleteIx' getUnique


-- | /O(n)/. Filter all elements that satisfy the predicate. In general, using
-- indexing operations is preferred, so instead of using 'filter' you should
-- construct an index that accomplishes this. This function will call the
-- provided predicate exactly once for each element in the 'IxSet'.
filter :: forall ixs a. Indexable ixs a => (a -> Bool) -> (IxSet ixs a -> IxSet ixs a)
filter f (IxSet a il) = IxSet a' il'
  where
    a' = Set.filter f a
    il' = mapIxList update il
      where
        update :: forall ix. Ix ix a -> Ix ix a
        update (Ix ix) = Ix (Ix.filterFrom a' ix)

--------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------

-- | Converts an 'IxSet' to a 'Set' of its elements.
toSet :: IxSet ixs a -> Set a
toSet (IxSet a _) = a

-- | Converts a 'Set' to an 'IxSet'.
fromSet :: forall ixs a. (Indexable ixs a) => Set a -> IxSet ixs a
fromSet set = IxSet set v
  where
    v :: IxList ixs a
    v = mapIxList mkIx mkEmptyIxList

    mkIx :: forall ix. (Indexed a ix, Ord ix) => Ix ix a -> Ix ix a
    mkIx (Ix _) = Ix (Ix.fromList [(k, x) | x <- Set.toList set, k <- ixFun x])

-- | Converts a list to an 'IxSet'.
fromList :: (Indexable ixs a) => [a] -> IxSet ixs a
fromList list = insertList list empty

-- | Returns the number of unique items in the 'IxSet'.
size :: IxSet ixs a -> Int
size = Set.size . toSet

-- | Converts an 'IxSet' to its list of elements.
toList :: IxSet ixs a -> [a]
toList = Set.toList . toSet

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in ascending order by the index 'ix'. When 'ix' values
-- are equivalent, the values will be sorted in ascending order by their 'Ord'
-- instance.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toAscList :: forall proxy ix ixs a. IsIndexOf ix ixs => proxy ix -> IxSet ixs a -> [a]
toAscList _ ixset = concatMap snd (groupAscBy ixset :: [(ix, [a])])

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in descending order by the index 'ix'. When 'ix' values
-- are equivalent, the values will be sorted in /ascending/ order by their 'Ord'
-- instance.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toDescList :: forall proxy ix ixs a. IsIndexOf ix ixs => proxy ix -> IxSet ixs a -> [a]
toDescList _ ixset = concatMap snd (groupDescBy ixset :: [(ix, [a])])

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in descending order by the index 'ix'. When 'ix' values
-- are equivalent, the values will be sorted in descending order by their 'Ord'
-- instance.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toFullDescList :: forall proxy ix ixs a. IsIndexOf ix ixs => proxy ix -> IxSet ixs a -> [a]
toFullDescList _ ixset = concatMap snd (groupFullDescBy ixset :: [(ix, [a])])

-- | If the 'IxSet' is a singleton it will return the one item stored in it.
-- If 'IxSet' is empty or has many elements this function returns 'Nothing'.
getOne :: IxSet ixs a -> Maybe a
getOne ixset = case toList ixset of
                   [x] -> Just x
                   _   -> Nothing

-- | Like 'getOne' with a user-provided default.
getOneOr :: a -> IxSet ixs a -> a
getOneOr def = fromMaybe def . getOne

-- | Like getOne, but error if multiple items exist

-- Throws: 'NotUniqueException
getUnique :: MonadThrow m => IxSet ixs a -> m (Maybe a)
getUnique ixset = case toList ixset of
                    [x] -> pure $ Just x
                    [] -> pure Nothing
                    _ -> throwM NotUnique

-- | Return 'True' if the 'IxSet' is empty, 'False' otherwise.
null :: IxSet ixs a -> Bool
null (IxSet a _) = Set.null a

--------------------------------------------------------------------------
-- Set operations
--------------------------------------------------------------------------

-- | An infix 'intersection' operation.
(&&&) :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
(&&&) = intersection

-- | An infix 'union' operation.
(|||) :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
(|||) = union

infixr 5 &&&
infixr 5 |||

-- | Takes the union of the two 'IxSet's.
union :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
union (IxSet a1 x1) (IxSet a2 x2)
  | Set.null a1 = IxSet a2 x2
  | Set.null a2 = IxSet a1 x1
  | otherwise = IxSet (Set.union a1 a2)
    (zipWithIxList' (\ (Ix a) (Ix b) -> Ix (Ix.union a b)) x1 x2)
-- TODO: function is taken from the first

-- | Takes the intersection of the two 'IxSet's.
intersection :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
intersection (IxSet a1 x1) (IxSet a2 x2) =
  IxSet (Set.intersection a1 a2)
    (zipWithIxList' (\ (Ix a) (Ix b) -> Ix (Ix.intersection a b)) x1 x2)

difference :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
difference (IxSet a1 x1) (IxSet a2 x2) =
  IxSet (Set.difference a1 a2)
    (zipWithIxList' (\(Ix a) (Ix b) -> Ix (Ix.difference a b)) x1 x2)
-- TODO: function is taken from the first

--------------------------------------------------------------------------
-- Query operations
--------------------------------------------------------------------------

-- | Infix version of 'getEQ'.
(@=) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> ix -> IxSet ixs a
ix @= v = getEQ v ix

-- | Infix version of 'getLT'.
(@<) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> ix -> IxSet ixs a
ix @< v = getLT v ix

-- | Infix version of 'getGT'.
(@>) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> ix -> IxSet ixs a
ix @> v = getGT v ix

-- | Infix version of 'getLTE'.
(@<=) :: (Indexable ixs a, IsIndexOf ix ixs)
      => IxSet ixs a -> ix -> IxSet ixs a
ix @<= v = getLTE v ix

-- | Infix version of 'getGTE'.
(@>=) :: (Indexable ixs a, IsIndexOf ix ixs)
      => IxSet ixs a -> ix -> IxSet ixs a
ix @>= v = getGTE v ix

-- | Returns the subset with indices in the open interval (k,k).
(@><) :: (Indexable ixs a, IsIndexOf ix ixs)
      => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @>< (v1,v2) = getLT v2 $ getGT v1 ix

-- | Returns the subset with indices in [k,k).
(@>=<) :: (Indexable ixs a, IsIndexOf ix ixs)
       => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @>=< (v1,v2) = getLT v2 $ getGTE v1 ix

-- | Returns the subset with indices in (k,k].
(@><=) :: (Indexable ixs a, IsIndexOf ix ixs)
       => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @><= (v1,v2) = getLTE v2 $ getGT v1 ix

-- | Returns the subset with indices in [k,k].
(@>=<=) :: (Indexable ixs a, IsIndexOf ix ixs)
        => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @>=<= (v1,v2) = getLTE v2 $ getGTE v1 ix

-- | Creates the subset that has an index in the provided list.
(@+) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> [ix] -> IxSet ixs a
ix @+ [e] = ix @= e
ix @+ list = List.foldl' union  empty $  map (ix @=) list

-- | Creates the subset that matches all the provided indices.
(@*) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> [ix] -> IxSet ixs a
ix @* [e]= ix @=  e
ix @* list = List.foldl' intersection ix $ map (ix @=) list

-- | Returns the subset with an index equal to the provided key.  The
-- set must be indexed over key type, doing otherwise results in
-- a compile error.

-- | Returns the subset with an index less than the provided key.  The
-- set must be indexed over key type, doing otherwise results in
-- a compile error.
getLT :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getLT = getOrd LT

-- | Returns the subset with an index greater than the provided key.
-- The set must be indexed over key type, doing otherwise results in
-- a compile error.
getGT :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getGT = getOrd GT

-- | Returns the subset with an index less than or equal to the
-- provided key.  The set must be indexed over key type, doing
-- otherwise results in a compile error.
getLTE :: (Indexable ixs a, IsIndexOf ix ixs)
       => ix -> IxSet ixs a -> IxSet ixs a
getLTE = getOrd2 True True False

-- | Returns the subset with an index greater than or equal to the
-- provided key.  The set must be indexed over key type, doing
-- otherwise results in a compile error.
getGTE :: (Indexable ixs a, IsIndexOf ix ixs)
       => ix -> IxSet ixs a -> IxSet ixs a
getGTE = getOrd2 False True True

-- | Returns the subset with an index within the interval provided.
-- The bottom of the interval is closed and the top is open,
-- i. e. [k1;k2).  The set must be indexed over key type, doing
-- otherwise results in a compile error.
getRange :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> ix -> IxSet ixs a -> IxSet ixs a
getRange k1 k2 ixset = getGTE k1 (getLT k2 ixset)

-- | Returns lists of elements paired with the indices determined by
-- type inference.
groupBy :: forall ix ixs a. IsIndexOf ix ixs => IxSet ixs a -> [(ix, [a])]
groupBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index) = map (second Set.toList) (Map.toList index)

-- | Returns the list of index keys being used for a particular index.
indexKeys :: forall ix ixs a . IsIndexOf ix ixs => IxSet ixs a -> [ix]
indexKeys (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [ix]
    f (Ix index) = Map.keys index

-- | Returns lists of elements paired with the indices determined by
-- type inference.
--
-- The resulting list will be sorted in ascending order by 'ix'.
-- The values in @[a]@ will be sorted in ascending order as well.
groupAscBy :: forall ix ixs a. IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupAscBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index) = map (second Set.toAscList) (Map.toAscList index)

-- | Returns lists of elements paired with the indices determined by
-- type inference.
--
-- The resulting list will be sorted in descending order by 'ix'.
-- The values in @[a]@ will, however, be sorted in /ascending/ order.
groupDescBy :: IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupDescBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index) = map (second Set.toAscList) (Map.toDescList index)

-- | Returns lists of elements paired with the indices determined by
-- type inference.
--
-- The resulting list will be sorted in descending order by 'ix'.
-- The values in @[a]@ will also be sorted in descending order.
groupFullDescBy :: IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupFullDescBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index) = map (second Set.toDescList) (Map.toDescList index)

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.  The set must be indexed over key type,
-- doing otherwise results in a compile error.

getOrd :: (Indexable ixs a, IsIndexOf ix ixs)
       => Ordering -> ix -> IxSet ixs a -> IxSet ixs a
getOrd LT = getOrd2 True False False
getOrd EQ = getEQ
getOrd GT = getOrd2 False False True

getEQ :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
        => ix -> IxSet ixs a -> IxSet ixs a
getEQ v (IxSet _ ixs) =  f (access ixs)
  where
    f :: Ix ix a -> IxSet ixs a
    f (Ix index) = maybe empty (fromMapOfSet v) $ Map.lookup v index

lookup :: forall ixs ix a. IsIndexOf ix ixs
        => ix -> IxSet ixs a -> Maybe a
lookup v (IxSet _ ixs) =  f (access ixs)
  where
    f :: Ix ix a -> Maybe a
    f (Ix index) = case Set.toList <$> (Map.lookup v index) of
                        Just [x] -> Just x
                        _ -> Nothing

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.  The set must be indexed over key type,
-- doing otherwise results in a compile error.
getOrd2 :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
        => Bool -> Bool -> Bool -> ix -> IxSet ixs a -> IxSet ixs a
getOrd2 inclt inceq incgt v (IxSet _ ixs) = f (access ixs)
  where
    f :: Ix ix a -> IxSet ixs a
    f (Ix index) = fromMapOfSets result
      where
        lt', gt' :: Map ix (Set a)
        eq' :: Maybe (Set a)
        (lt', eq', gt') = Map.splitLookup v index

        lt, gt :: Map ix (Set a)
        lt = if inclt then lt' else Map.empty
        gt = if incgt then gt' else Map.empty
        eq :: Maybe (Set a)
        eq = if inceq then eq' else Nothing

        ltgt :: Map ix (Set a)
        ltgt = Map.unionWith Set.union lt gt

        result :: Map ix (Set a)
        result = case eq of
          Just eqset -> Map.insertWith Set.union v eqset ltgt
          Nothing    -> ltgt

--------------------------------------------------------------------------
-- Joins
--------------------------------------------------------------------------

newtype Joined a b = Joined (a, b) deriving (Show, Read, Eq, Ord)

instance (Indexed a ix, Indexed b ix) => Indexed (Joined a b) ix where
  ixFun (Joined (a, b)) = ixFun a <> ixFun b

-- | Perform an inner join between two tables using a specific index. The
-- expression @'innerJoinUsing' s1 s2 (Proxy :: Proxy t)@ is similar in purpose
-- to the SQL expression @SELECT * FROM s1 INNER JOIN s2 USING (t)@. The
-- resulting 'IxSet' can contain any index type @ix@ for which the instances
-- @'Indexed' a ix@ and @'Indexed' b ix@ exist.
innerJoinUsing ::
     forall ixs1 ixs2 ixs3 a b proxy ix.
     (Indexable ixs3 (Joined a b), IsIndexOf ix ixs1, IsIndexOf ix ixs2, IsIndexOf ix ixs3)
  => IxSet ixs1 a
  -> IxSet ixs2 b
  -> proxy ix
  -> IxSet ixs3 (Joined a b)
innerJoinUsing (IxSet _ ixs1) (IxSet _ ixs2) _ = f (access ixs1) (access ixs2)
  where
    f :: Ix ix a -> Ix ix b -> IxSet ixs3 (Joined a b)
    f (Ix m1) (Ix m2) =
      fromMapOfSets
        (MM.merge MM.dropMissing MM.dropMissing (MM.zipWithMatched (\_ a b -> Set.mapMonotonic Joined (Set.cartesianProduct a b))) m1 m2)

-- Optimization todo:
--
--   * can we avoid rebuilding the collection every time we query?
--     does laziness take care of everything?
--
--   * nicer operators?
--
--   * nice way to do updates that doesn't involve reinserting the entire data
--
--   * can we index on xpath rather than just type?

-- | Statistics about 'IxSet'. This function returns quadruple
-- consisting of
--
--   1. total number of elements in the set
--   2. number of declared indices
--   3. number of keys in all indices
--   4. number of values in all keys in all indices.
--
-- This can aid you in debugging and optimisation.
--
stats :: Indexable ixs a => IxSet ixs a -> (Int,Int,Int,Int)
stats (IxSet a ixs) = (no_elements,no_indexes,no_keys,no_values)
    where
      no_elements = Set.size a
      no_indexes  = lengthIxList ixs
      no_keys     = sum (ixListToList (\ (Ix m) -> Map.size m) ixs)
      no_values   = sum (ixListToList (\ (Ix m) -> sum [Set.size s | s <- Map.elems m]) ixs)

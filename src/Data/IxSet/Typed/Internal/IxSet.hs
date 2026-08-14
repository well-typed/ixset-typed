{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{- |

This module defines the main 'IxSet' type.

NB: this is internal to @Data.IxSet.Typed@ and is subject to change.

-}
module Data.IxSet.Typed.Internal.IxSet
    (
     -- * Set type
     IxSet(..),

     -- * Changes to set
     IndexOp,
     SetOp,
     change,
     insert,
     insertList,
     insertSet,
     insertMany,
     delete,
     deleteSet,
     deleteMany,
     updateIx,
     deleteIx,

     -- * Creation
     empty,
     fromSet,
     fromList,

     -- * Conversion
     toSet,
     toList,
     toAscList,
     toDescList,
     getOne,
     getOneOr,

     -- * Size checking
     size,
     null,

     -- * Set operations
     (&&&),
     (|||),
     (\\\),
     union,
     intersection,
     difference,
     filter,

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
     getLT,
     getGT,
     getLTE,
     getGTE,
     getRange,

     -- * Grouping
     getIxMap,
     groupBy,
     groupAscBy,
     groupDescBy,
     indexKeys,

     -- * Debugging and optimization
     forceIndices,
     stats
)
where

import Data.Kind
import Prelude hiding (filter, null)

import           Control.Arrow  (first, second)
import           Control.DeepSeq (NFData(..))
import qualified Data.Foldable  as Fold
import qualified Data.IxSet.Typed.Internal.Ix  as Ix
import           Data.IxSet.Typed.Internal.Ix  (Ix(Ix), IxMap)
import           Data.IxSet.Typed.Internal.IxList
import qualified Data.List      as List
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Maybe     (fromMaybe)
import           Data.SafeCopy  (SafeCopy(..), contain, safeGet, safePut)
import           Data.Set       (Set)
import qualified Data.Set       as Set
import           Data.Typeable  (Typeable)

--------------------------------------------------------------------------
-- The main 'IxSet' datatype.
--------------------------------------------------------------------------

-- | Set with associated indices.
--
-- The type-level list 'ixs' contains all types that are valid index keys. The
-- type 'a' is the type of elements in the indexed set.
--
data IxSet (ixs :: [Type]) (a :: Type) where
  IxSet :: !(Set a) -> IxList ixs a -> IxSet ixs a


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

instance (Indexable ixs a, Typeable ixs, SafeCopy a, Typeable a) => SafeCopy (IxSet ixs a) where
  putCopy = contain . safePut . toList
  getCopy = contain $ fmap fromList safeGet

instance (All NFData ixs, NFData a) => NFData (IxSet ixs a) where
  rnf (IxSet a ixs) = rnf a `seq` rnf ixs

instance Indexable ixs a => Semigroup (IxSet ixs a) where
  (<>) = union

instance Indexable ixs a => Monoid (IxSet ixs a) where
  mempty  = empty
  mappend = (<>)

instance Foldable (IxSet ixs) where
  fold      = Fold.fold      . toSet
  foldMap f = Fold.foldMap f . toSet
  foldr f z = Fold.foldr f z . toSet
  foldl f z = Fold.foldl f z . toSet


--------------------------------------------------------------------------
-- 'IxSet' construction
--------------------------------------------------------------------------

-- | An empty 'IxSet'.
empty :: Indexable ixs a => IxSet ixs a
empty = IxSet Set.empty indices


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
--
-- This will update the indices strictly.
--
change :: forall ixs a. Indexable ixs a
       => SetOp -> IndexOp -> a -> IxSet ixs a -> IxSet ixs a
change opS opI x = changeAll (opS x) update
  where
    update :: forall ix. Ord ix => Ix ix a -> Ix ix a
    update (Ix index f) = Ix index' f
      where
        ds :: [ix]
        ds = f x
        ii :: forall k. Ord k => Map k (Set a) -> k -> Map k (Set a)
        ii m dkey = opI dkey x m
        index' :: Map ix (Set a)
        index' = List.foldl' ii index ds

-- | Higher-order operator for modifying 'IxSet's.
--
-- This will update the indices strictly.
--
changeAll :: All Ord ixs
          => (Set a -> Set a)
          -> (forall ix. Ord ix => Ix ix a -> Ix ix a)
          -> IxSet ixs a -> IxSet ixs a
changeAll f g (IxSet set indexes) = IxSet (f set) $! mapIxList' g indexes

-- | Insert a list of elements into an 'IxSet'.  (See also 'insertMany'.)
--
-- This will update the indices strictly.
--
insertList :: forall ixs a. Indexable ixs a
           => [a] -> IxSet ixs a -> IxSet ixs a
insertList = insertMany

-- | Insert a 'Set' of elements into an 'IxSet'.
--
-- This will update the indices strictly.
--
insertSet :: forall ixs a. (Indexable ixs a)
           => Set a -> IxSet ixs a -> IxSet ixs a
insertSet xs = changeAll (Set.union xs) (Ix.insertMany xs)

-- | Insert a 'Foldable' collection of elements into an 'IxSet'.
--
-- This will update the indices strictly.
--
insertMany :: forall ixs f a. (Indexable ixs a, Foldable f)
           => f a -> IxSet ixs a -> IxSet ixs a
insertMany xs = changeAll (\ a -> Fold.foldl' (\ b x -> Set.insert x b) a xs) (Ix.insertMany xs)

-- | Inserts an item into the 'IxSet'.
--
-- If your data happens to have a primary key this function might not be what
-- you want, because it allows two values to coexist in the set with the same
-- primary key. See 'updateIx'.
--
-- This will update the indices strictly.
--
insert :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
insert = change Set.insert Ix.insert

-- | Removes an item from the 'IxSet'.
--
-- This will update the indices strictly.
--
delete :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
delete = change Set.delete Ix.delete

-- | Remove every element of a 'Set' from an 'IxSet'.
--
-- This will update the indices strictly.
--
deleteSet :: Indexable ixs a => Set a -> IxSet ixs a -> IxSet ixs a
deleteSet deletes = changeAll (`Set.difference` deletes) (Ix.deleteMany deletes)

-- | Remove every element of a 'Foldable' collection from an 'IxSet'.
--
-- This will update the indices strictly.
--
deleteMany :: (Indexable ixs a, Foldable t) => t a -> IxSet ixs a -> IxSet ixs a
deleteMany deletes = changeAll (\ s -> Fold.foldl' (flip Set.delete) s deletes) (Ix.deleteMany deletes)

-- | Replace the item with the given index of type 'ix'. Only works if there is
-- at most one item with that index in the 'IxSet'.
--
-- If you have more than one item with given index, the new item will be
-- inserted in addition to the existing items.  (NB: this is contrary to the
-- documentation in previous versions of @ixset-typed@ and @ixset@, which
-- incorrectly claimed the set would not be modified in this case.)
--
-- This will update the indices strictly.
--
updateIx :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> a -> IxSet ixs a -> IxSet ixs a
updateIx i new ixset = insert new $
                     maybe ixset (flip delete ixset) $
                     getOne $ ixset @= i

-- | Delete the item with the given index of type 'ix'. Only works if there is
-- at most one item with that index in the 'IxSet'.
--
-- Will not change 'IxSet' if you have more than one item with given index.
--
-- This will update the indices strictly.
--
deleteIx :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> IxSet ixs a -> IxSet ixs a
deleteIx i ixset = maybe ixset (flip delete ixset) $
                       getOne $ ixset @= i


--------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------

-- | Converts an 'IxSet' to a 'Set' of its elements.
toSet :: IxSet ixs a -> Set a
toSet (IxSet a _) = a

-- | Converts a 'Set' to an 'IxSet'.
--
-- This is strict in the 'Set' but lazy in the construction of indices, so they
-- are not built until needed.
--
fromSet :: forall ixs a. (Indexable ixs a) => Set a -> IxSet ixs a
fromSet s = IxSet s makeIndices
  where
    makeIndices :: IxList ixs a
    makeIndices = mapIxList (Ix.insertMany s) indices

-- | Converts a list to an 'IxSet'.
--
-- This is spine-strict in the list of elements but lazy in the construction of
-- indices, so they are not built until needed.
--
fromList :: (Indexable ixs a) => [a] -> IxSet ixs a
fromList = fromSet . Set.fromList

-- | Returns the number of unique items in the 'IxSet'.
size :: IxSet ixs a -> Int
size = Set.size . toSet

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in ascending order by the @'Ord' a@ instance.
--
toList :: IxSet ixs a -> [a]
toList = Set.toList . toSet

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in ascending order by the index 'ix'.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toAscList :: forall proxy ix ixs a. IsIndexOf ix ixs => proxy ix -> IxSet ixs a -> [a]
toAscList _ ixset = concatMap snd (groupAscBy ixset :: [(ix, [a])])

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in descending order by the index 'ix'.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toDescList :: forall proxy ix ixs a. IsIndexOf ix ixs => proxy ix -> IxSet ixs a -> [a]
toDescList _ ixset = concatMap snd (groupDescBy ixset :: [(ix, [a])])

-- | If the 'IxSet' is a singleton it will return the one item stored in it.
-- If 'IxSet' is empty or has many elements this function returns 'Nothing'.
getOne :: IxSet ixs a -> Maybe a
getOne ixset = case toList ixset of
                   [x] -> Just x
                   _   -> Nothing

-- | Like 'getOne' with a user-provided default.
getOneOr :: a -> IxSet ixs a -> a
getOneOr def = fromMaybe def . getOne

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

-- | An infix 'difference' operation.
(\\\) :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
(\\\) = difference

infixr 5 &&&
infixr 5 |||

-- | Takes the union of the two 'IxSet's.
--
-- This will update the indices lazily.
--
union :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
union (IxSet a1 x1) (IxSet a2 x2) =
  IxSet (Set.union a1 a2) (zipWithIxList Ix.union x1 x2)

-- | Takes the intersection of the two 'IxSet's.
--
-- This will update the indices lazily.
--
intersection :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
intersection (IxSet a1 x1) (IxSet a2 x2) =
  IxSet (Set.intersection a1 a2) (zipWithIxList Ix.intersection x1 x2)

-- | Remove every item in the second 'IxSet' from the first 'IxSet'.
--
-- This will update the indices lazily.
--
difference :: forall ixs a. Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
difference (IxSet elements ixs) (IxSet deletes deleteIxs) =
  IxSet (elements `Set.difference` deletes) (zipWithIxList Ix.difference ixs deleteIxs)

-- | Limit elements of an `IxSet` to those matching a predicate.
--
-- This will update the indices lazily.
--
filter :: Indexable ixs a => (a -> Bool) -> IxSet ixs a -> IxSet ixs a
filter p (IxSet elements indexes) =
    IxSet good_elements (mapIxList (Ix.deleteMany bad_elements) indexes)
  where
    (good_elements, bad_elements) = Set.partition p elements

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
ix @+ list = List.foldl' union empty $ map (ix @=) list

-- | Creates the subset that matches all the provided indices.
(@*) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> [ix] -> IxSet ixs a
ix @* list = List.foldl' intersection ix $ map (ix @=) list

-- | Returns the subset with an index equal to the provided key.
getEQ :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getEQ = getOrd EQ

-- | Returns the subset with an index less than the provided key.
getLT :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getLT = getOrd LT

-- | Returns the subset with an index greater than the provided key.
getGT :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getGT = getOrd GT

-- | Returns the subset with an index less than or equal to the
-- provided key.
getLTE :: (Indexable ixs a, IsIndexOf ix ixs)
       => ix -> IxSet ixs a -> IxSet ixs a
getLTE = getOrd2 True True False

-- | Returns the subset with an index greater than or equal to the
-- provided key.
getGTE :: (Indexable ixs a, IsIndexOf ix ixs)
       => ix -> IxSet ixs a -> IxSet ixs a
getGTE = getOrd2 False True True

-- | Returns the subset with an index within the interval provided.
-- The bottom of the interval is closed and the top is open,
-- i.e. [k1,k2).
getRange :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> ix -> IxSet ixs a -> IxSet ixs a
getRange k1 k2 ixset = getGTE k1 (getLT k2 ixset)

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.
getOrd :: (Indexable ixs a, IsIndexOf ix ixs)
       => Ordering -> ix -> IxSet ixs a -> IxSet ixs a
getOrd LT = getOrd2 True False False
getOrd EQ = getOrd2 False True False
getOrd GT = getOrd2 False False True

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.
getOrd2 :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
        => Bool -> Bool -> Bool -> ix -> IxSet ixs a -> IxSet ixs a
getOrd2 inclt inceq incgt v = fromMapOfSets . select . getIxMap
  where
    select :: IxMap ix a -> IxMap ix a
    select index = result
      where
        lt', gt' :: IxMap ix a
        eq' :: Maybe (Set a)
        (lt', eq', gt') = Map.splitLookup v index

        lt, gt :: IxMap ix a
        lt = if inclt then lt' else Map.empty
        gt = if incgt then gt' else Map.empty
        eq :: Maybe (Set a)
        eq = if inceq then eq' else Nothing

        ltgt :: IxMap ix a
        ltgt = Map.unionWith Set.union lt gt

        result :: IxMap ix a
        result = case eq of
          Just eqset -> Map.insertWith Set.union v eqset ltgt
          Nothing    -> ltgt

-- | Internal helper function that takes a partial index from one index
-- set and rebuilds the rest of the structure of the index set.
--
-- We try to be really clever here. The partialindex is a Map of Sets
-- from original index. We want to reuse it as much as possible. If there
-- was a guarantee that each element is present at at most one key we
-- could reuse originalindex as it is. But there can be more, so we need to
-- add remaining ones (in updateh). Anyway we try to reuse old structure and
-- keep new allocations low as much as possible.
--
-- This is used by queries, so it produces the indices lazily.
--
fromMapOfSets :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
              => IxMap ix a -> IxSet ixs a
fromMapOfSets partialindex =
    IxSet a (mapAt updateh updatet indices)
  where
    a :: Set a
    a = Set.unions partialindex

    -- Update function for the index corresponding to partialindex.
    -- Any key already in the partial index is there with its full
    -- set of elements, so only the other keys need adding.
    updateh :: Ix ix a -> Ix ix a
    updateh (Ix _ f) = Ix.insertManyWith (\ k -> Map.notMember k partialindex) a f partialindex

    -- Update function for all other indices.
    updatet :: forall ix'. Ord ix' => Ix ix' a -> Ix ix' a
    updatet (Ix _ f) = Ix.build a f


--------------------------------------------------------------------------
-- Grouping operations
--------------------------------------------------------------------------

-- | Extract a single index map from an 'IxSet'.
getIxMap :: forall ixs ix a . IsIndexOf ix ixs => IxSet ixs a -> Ix.IxMap ix a
getIxMap (IxSet _ ixs) = case access ixs of
    Ix m _ -> m

-- | Returns lists of elements paired with the indices determined by
-- type inference.
groupBy :: forall ix ixs a. IsIndexOf ix ixs => IxSet ixs a -> [(ix, [a])]
groupBy = map (second Set.toList) . Map.toList . getIxMap

-- | Returns the list of index keys being used for a particular index.
indexKeys :: forall ix ixs a . IsIndexOf ix ixs => IxSet ixs a -> [ix]
indexKeys = Map.keys . getIxMap

-- | Returns lists of elements paired with the indices determined by
-- type inference.
--
-- The resulting list will be sorted in ascending order by 'ix'.
-- The values in @[a]@ will be sorted in ascending order as well.
groupAscBy :: forall ix ixs a. IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupAscBy = map (second Set.toAscList) . Map.toAscList . getIxMap

-- | Returns lists of elements paired with the indices determined by
-- type inference.
--
-- The resulting list will be sorted in descending order by 'ix'.
--
-- NOTE: The values in @[a]@ are currently sorted in ascending
-- order. But this may change if someone bothers to add
-- 'Set.toDescList'. So do not rely on the sort order of the
-- resulting list.
groupDescBy :: IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupDescBy = map (second Set.toAscList) . Map.toDescList . getIxMap


--------------------------------------------------------------------------
-- Debugging and optimization
--------------------------------------------------------------------------

-- | Evaluate the indices contained within an 'IxSet'.  Call this after a lazy
-- operation such as 'fromSet', 'fromList' or a query, to perform the work of
-- building the indices immediately rather than deferring it until they are
-- used.  The underlying 'Set' does not need to be forced as it is stored
-- spine-strictly.
--
forceIndices :: IxSet ixs a -> IxSet ixs a
forceIndices (IxSet set ixlist) = IxSet set $! forceIxList ixlist


-- Optimization todo:
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
-- Evaluating the third or fourth components of the quadruple will
-- cause the indices to be forced (cf. 'forceIndices').
--
stats :: IxSet ixs a -> (Int,Int,Int,Int)
stats (IxSet a ixs) = (no_elements,no_indexes,no_keys,no_values)
    where
      no_elements = Set.size a
      no_indexes  = lengthIxList ixs
      no_keys     = foldlIxList' (\ n (Ix m _) -> n + Map.size m) 0 ixs
      no_values   = foldlIxList' (\ n (Ix m _) -> Fold.foldl' (\ acc s -> acc + Set.size s) n m) 0 ixs

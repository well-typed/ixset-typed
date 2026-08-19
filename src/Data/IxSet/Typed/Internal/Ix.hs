{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK not-home #-}


{- |

This module defines the t'Ix' type of indices.

= WARNING

This module exposes internal implementation details of @ixset-typed@.  It allows
invariants to be broken via direct access to datatype constructors, and is
subject to change without warning in future releases.

-}
module Data.IxSet.Typed.Internal.Ix
    ( Ix(..)
    , IxMap
    , insert
    , insertMany
    , delete
    , build
    , insertManyWith
    , deleteMany
    , difference
    , union
    , intersection
    )
    where

import           Control.DeepSeq (NFData(..))
import           Control.Monad (guard)
import qualified Data.Foldable as Fold
import           Data.Kind  (Type)
import qualified Data.List  as List
import           Data.Map   (Map)
import qualified Data.Map.Strict as Map.Strict
import qualified Data.Map.Merge.Strict as Map.Strict
import           Data.Set   (Set)
import qualified Data.Set   as Set

-- the core datatypes

-- | The map underlying an t'Ix', i.e. a 'Map' from some key (of type @ix@) to a
-- 'Set' of values (of type @a@) for that key.
--
-- Invariant: the 'Set's are never empty.
--
type IxMap ix a = Map ix (Set a)

-- | An index, which consists of an 'Map' from index values to 'Set's of
-- elements with that index value, and a projection function mapping an element
-- to a list of its index values.
--
-- Forcing an t'Ix' should compute at least the spine of the underlying 'Map'.
--
data Ix (ix :: Type) (a :: Type) where
  Ix :: !(IxMap ix a) -> (a -> [ix]) -> Ix ix a

instance (NFData ix, NFData a) => NFData (Ix ix a) where
  rnf (Ix m f) = rnf m `seq` f `seq` ()

-- modification operations

-- | Convenience function for inserting into 'Map's of 'Set's as in
-- the case of an t'Ix'.  If they key did not already exist in the
-- 'Map', then a new 'Set' is added transparently.
insert :: (Ord a, Ord ix)
       => ix -> a -> IxMap ix a -> IxMap ix a
insert k v index = Map.Strict.insertWith Set.union k (Set.singleton v) index

-- | Insert a 'Foldable' collection of elements into an index, under the
-- keys given for each of them by the indexing function, but ignoring any
-- key that does not satisfy the predicate.
insertManyWith :: (Foldable f, Ord a, Ord ix)
               => (ix -> Bool) -> f a -> (a -> [ix])
               -> IxMap ix a -> Ix ix a
insertManyWith p xs f index =
    Ix (Fold.foldl' (\ m v -> List.foldl' (ins v) m (f v)) index xs) f
  where
    ins v m k = if p k then insert k v m else m

-- | Create a new index from a 'Foldable' collection of elements.
build :: (Foldable f, Ord a, Ord ix) => f a -> (a -> [ix]) -> Ix ix a
build xs f = insertManyWith (const True) xs f Map.Strict.empty

-- | Insert a 'Foldable' collection of elements into an t'Ix'.
insertMany :: (Foldable f, Ord a, Ord ix) => f a -> Ix ix a -> Ix ix a
insertMany xs (Ix index f) = insertManyWith (const True) xs f index

-- | Convenience function for deleting from 'Map's of 'Set's. If the
-- resulting 'Set' is empty, then the entry is removed from the 'Map'.
delete :: forall a ix . (Ord a, Ord ix)
       => ix -> a -> IxMap ix a -> IxMap ix a
delete k v index = Map.Strict.update remove k index
  where
    remove :: Set a -> Maybe (Set a)
    remove = dropIfEmpty . Set.delete v

-- | Helper function to delete a collection of elements from an index.
deleteMany :: (Ord a, Ord ix, Foldable f) => f a -> Ix ix a -> Ix ix a
deleteMany deletes (Ix index f) = Ix index' f
  where
    index' = Fold.foldl' (\ m v -> List.foldl' (\ m' k -> delete k v m') m (f v)) index deletes

-- | Takes the union of two indices.  The projection function is assumed to be
-- the same.
--
-- This is strict, so that once the index is forced it will be recomputed in
-- full. The caller ('Data.IxSet.Typed.union') will avoid forcing it until
-- needed.
--
union :: (Ord a, Ord ix)
      => Ix ix a -> Ix ix a -> Ix ix a
union (Ix a f) (Ix b _) = Ix (Map.Strict.unionWith Set.union a b) f

-- | Takes the intersection of two indices.  The projection function is assumed
-- to be the same.
--
-- This is strict, so that once the index is forced it will be recomputed in
-- full. The caller ('Data.IxSet.Typed.intersection') will avoid forcing it
-- until needed.
--
intersection :: (Ord a, Ord ix)
             => Ix ix a -> Ix ix a -> Ix ix a
intersection (Ix a f) (Ix b _) = Ix (intersectionIxMap a b) f

-- | Takes the intersection of two index maps (strictly).
intersectionIxMap :: (Ord a, Ord ix)
                  => IxMap ix a -> IxMap ix a -> IxMap ix a
intersectionIxMap = Map.Strict.merge
  Map.Strict.dropMissing
  Map.Strict.dropMissing
  (Map.Strict.zipWithMaybeMatched $ \_ els1 els2 ->
    dropIfEmpty (Set.intersection els1 els2)
  )

-- | Deletes the values in the second index from the first.  The projection
-- function is assumed to be the same.
--
-- This is strict, so that once the index is forced it will be recomputed in
-- full. The caller ('Data.IxSet.Typed.difference') will avoid forcing it until
-- needed.
--
difference :: (Ord a, Ord ix)
           => Ix ix a -> Ix ix a -> Ix ix a
difference (Ix a f) (Ix b _) = Ix (differenceIxMap a b) f

-- | Deletes the second index map from the first.
differenceIxMap :: (Ord a, Ord ix)
                => IxMap ix a -> IxMap ix a -> IxMap ix a
differenceIxMap = Map.Strict.merge
  Map.Strict.preserveMissing
  Map.Strict.dropMissing
  (Map.Strict.zipWithMaybeMatched $ \_ els dels ->
    dropIfEmpty (els `Set.difference` dels)
  )

-- | Check a set is non-empty.  This is used to maintain the invariant that an
-- 'IxMap' never contains an empty set.
dropIfEmpty :: Set a -> Maybe (Set a)
dropIfEmpty s = s <$ guard (not (Set.null s))

module Data.IxSet.Typed.Ix
    ( Ix(..)
    , insert
    , delete
    , fromList
    , insertList
    , deleteList
    , union
    , intersection
    , difference
    , filterFrom
    )
    where

import Control.DeepSeq
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding (filter)

-- the core data types

-- | 'Ix' is a 'Map' from some key (of type 'ix') to a 'Set' of
-- values (of type 'a') for that key.
newtype Ix ix a = Ix (Map ix (Set a))

instance (NFData ix, NFData a) => NFData (Ix ix a) where
  rnf (Ix m) = rnf m `seq` ()

-- modification operations

-- | Convenience function for inserting into 'Map's of 'Set's as in
-- the case of an 'Ix'.  If the key did not already exist in the
-- 'Map', then a new 'Set' is added transparently.
insert :: (Ord a, Ord k)
       => k -> a -> Map k (Set a) -> Map k (Set a)
insert k v index = Map.alter (Just . maybe (Set.singleton v) (Set.insert v)) k index
{-# INLINE insert #-}

-- | Helper function to 'insert' a list of elements into a set.
insertList :: (Ord a, Ord k)
           => [(k,a)] -> Map k (Set a) -> Map k (Set a)
insertList xs index = List.foldl' (\m (k,v)-> insert k v m) index xs
{-# INLINE insertList #-}

-- | Helper function to create a new index from a list.
fromList :: (Ord a, Ord k) => [(k, a)] -> Map k (Set a)
fromList xs =
  List.foldl' (\m (k,v) -> insert k v m)  Map.empty  xs
{-# INLINE fromList #-}

-- | Convenience function for deleting from 'Map's of 'Set's. If the
-- resulting 'Set' is empty, then the entry is removed from the 'Map'.
delete :: (Ord a, Ord k)
       => k -> a -> Map k (Set a) -> Map k (Set a)
delete k v index = Map.update remove k index
    where
    remove set = let set' = Set.delete v set
                 in if Set.null set' then Nothing else Just set'

-- | Helper function to 'delete' a list of elements from a set.
deleteList :: (Ord a, Ord k)
           => [(k,a)] -> Map k (Set a) -> Map k (Set a)
deleteList xs index = List.foldl' (\m (k,v) -> delete k v m) index xs

-- | Takes the union of two sets.
union :: (Ord a, Ord k)
       => Map k (Set a) -> Map k (Set a) -> Map k (Set a)
union index1 index2 = Map.unionWith Set.union index1 index2

-- | Takes the intersection of two sets.
intersection :: (Ord a, Ord k)
             => Map k (Set a) -> Map k (Set a) -> Map k (Set a)
intersection index1 index2 = Map.filter (not . Set.null) $
                             Map.intersectionWith Set.intersection index1 index2

-- | Takes the difference of two sets.
difference :: (Ord a, Ord k)
             => Map k (Set a) -> Map k (Set a) -> Map k (Set a)
difference index1 index2 = Map.differenceWith diff index1 index2
  where diff set1 set2 = let diffSet = Set.difference set1 set2 in
                            if Set.null diffSet then Nothing else Just diffSet

-- | Filters the sets by restricting to the elements in the provided set.
filterFrom :: (Ord a) => Set a -> Map k (Set a) -> Map k (Set a)
filterFrom s index = Map.mapMaybe g index
  where g set = let set' = Set.intersection set s
                in if Set.null set' then Nothing else Just set'

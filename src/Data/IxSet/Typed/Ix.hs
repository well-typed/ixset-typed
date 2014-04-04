{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleInstances,
             MultiParamTypeClasses, TemplateHaskell, PolymorphicComponents,
             DeriveDataTypeable,ExistentialQuantification, KindSignatures,
             StandaloneDeriving, GADTs #-}

{- |

This module defines 'Typeable' indexes and convenience functions. Should
probably be considered private to @Data.IxSet.Typed@.

-}
module Data.IxSet.Typed.Ix
    ( Ix(..)
    , IsIndex(..)
    , insert
    , delete
    , fromList
    , insertList
    , deleteList
    , union
    , intersection
    )
    where

import           Control.DeepSeq
-- import           Data.Generics hiding (GT)
-- import qualified Data.Generics.SYB.WithClass.Basics as SYBWC
import qualified Data.List       as List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set

-- the core datatypes

-- | 'Ix' is a 'Map' from some key (of type 'ix') to a 'Set' of
-- values (of type 'a') for that key.
data Ix (ix :: *) (a :: *) where
  Ix :: !(Map ix (Set a)) -> Ix ix a

class Ord ix => IsIndex a ix where
  keys :: a -> [ix]

instance (NFData ix, NFData a) => NFData (Ix ix a) where
  rnf (Ix m) = rnf m

-- deriving instance Typeable (Ix ix a)

{-
 -- minimal hacky instance
instance Data a => Data (Ix a) where
    toConstr (Ix _ _) = con_Ix_Data
    gunfold _ _     = error "gunfold"
    dataTypeOf _    = ixType_Data
-}

{-
con_Ix_Data :: Constr
con_Ix_Data = mkConstr ixType_Data "Ix" [] Prefix
ixType_Data :: DataType
ixType_Data = mkDataType "Happstack.Data.IxSet.Ix" [con_Ix_Data]
-}

{-
ixConstr :: SYBWC.Constr
ixConstr = SYBWC.mkConstr ixDataType "Ix" [] SYBWC.Prefix
ixDataType :: SYBWC.DataType
ixDataType = SYBWC.mkDataType "Ix" [ixConstr]
-}

{-
instance (SYBWC.Data ctx a, SYBWC.Sat (ctx (Ix a)))
       => SYBWC.Data ctx (Ix a) where
    gfoldl = error "gfoldl Ix"
    toConstr _ (Ix _ _)    = ixConstr
    gunfold = error "gunfold Ix"
    dataTypeOf _ _ = ixDataType
-}

-- modification operations

-- | Convenience function for inserting into 'Map's of 'Set's as in
-- the case of an 'Ix'.  If they key did not already exist in the
-- 'Map', then a new 'Set' is added transparently.
insert :: (Ord a, Ord k)
       => k -> a -> Map k (Set a) -> Map k (Set a)
insert k v index = Map.insertWith Set.union k (Set.singleton v) index

-- | Helper function to 'insert' a list of elements into a set.
insertList :: (Ord a, Ord k)
           => [(k,a)] -> Map k (Set a) -> Map k (Set a)
insertList xs index = List.foldl' (\m (k,v)-> insert k v m) index xs

-- | Helper function to create a new index from a list.
fromList :: (Ord a, Ord k) => [(k, a)] -> Map k (Set a)
fromList xs =
  Map.fromListWith Set.union (List.map (\ (k, v) -> (k, Set.singleton v)) xs)

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


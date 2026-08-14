{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{- |

This module defines the 'IxList' type of lists of indices.

NB: this is internal to @Data.IxSet.Typed@ and is subject to change.

-}
module Data.IxSet.Typed.Internal.IxList
    ( IxList(..)
    , (!:::)
    , All
    , IsIndexOf(..)
    , Indexable(..)
    , lengthIxList
    , foldlIxList'
    , mapIxList
    , mapIxList'
    , zipWithIxList
    , forceIxList
    ) where

import Control.DeepSeq (NFData(..))
import Data.Kind (Type, Constraint)
import Prelude hiding (filter, null)

import Data.IxSet.Typed.Internal.Ix (Ix)

data IxList (ixs :: [Type]) (a :: Type) where
  Nil   :: IxList '[] a
  (:::) :: Ix ix a -> IxList ixs a -> IxList (ix ': ixs) a

infixr 5 :::

instance (All NFData ixs, NFData a) => NFData (IxList ixs a) where
  rnf Nil        = ()
  rnf (x ::: xs) = rnf x `seq` rnf xs


-- | A strict variant of ':::'.
(!:::) :: Ix ix a -> IxList ixs a -> IxList (ix ': ixs) a
(!:::) !ix !ixs = ix ::: ixs

infixr 5 !:::


--------------------------------------------------------------------------
-- Type-level tools for dealing with indexed sets.
--
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
type All :: (Type -> Constraint) -> [Type] -> Constraint
type family All c xs :: Constraint where
  All c '[]       = ()
  All c (x ': xs) = (c x, All c xs)

-- | Associate indices with a given type. The constraint
-- @'Indexable' ixs a@ says that we know how to build index sets
-- of type @'IxSet' ixs a@.
--
-- In order to use an 'IxSet' on a particular type, you have to
-- make it an instance of 'Indexable' yourself. There are no
-- predefined instances of 'IxSet'.
--
class (All Ord ixs, Ord a) => Indexable ixs a where

  -- | Define how the indices for this particular type should look like.
  --
  -- Use the 'ixList' function to construct the list of indices, and use
  -- 'ixFun' (or 'ixGen') for individual indices.
  indices :: IxList ixs a

-- | Constraint for membership in the type-level list. Says that 'ix'
-- is contained in the index list 'ixs'.
class Ord ix => IsIndexOf (ix :: Type) (ixs :: [Type]) where

  -- | Provide access to the selected index in the list.
  access :: IxList ixs a -> Ix ix a

  -- | Map over the index list, treating the selected different
  -- from the rest.
  --
  -- The function 'mapAt' is lazy in the index list structure,
  -- because it is used by query operations.
  mapAt :: (All Ord ixs)
        => (Ix ix a -> Ix ix a)
              -- ^ what to do with the selected index
        -> (forall ix'. Ord ix' => Ix ix' a -> Ix ix' a)
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
lengthIxList = foldlIxList' (\ n _ -> succ n) 0

-- | Strict left fold over an index list.
foldlIxList' :: forall ixs a b. (forall ix . b -> Ix ix a -> b) -> b -> IxList ixs a -> b
foldlIxList' c = go
  where
    go :: forall ixs'. b -> IxList ixs' a -> b
    go !acc Nil        = acc
    go !acc (x ::: xs) = go (c acc x) xs

-- | Map over an index list.
mapIxList :: All Ord ixs
          => (forall ix. Ord ix => Ix ix a -> Ix ix a)
                -- ^ what to do with each index
          -> IxList ixs a -> IxList ixs a
mapIxList _ Nil        = Nil
mapIxList f (x ::: xs) = f x ::: mapIxList f xs

-- | Map over an index list (spine-strict).
mapIxList' :: All Ord ixs
           => (forall ix. Ord ix => Ix ix a -> Ix ix a)
                 -- ^ what to do with each index
           -> IxList ixs a -> IxList ixs a
mapIxList' _ Nil        = Nil
mapIxList' f (x ::: xs) = f x !::: mapIxList' f xs

-- | Zip two index lists of compatible type (lazy).
zipWithIxList :: All Ord ixs
              => (forall ix. Ord ix => Ix ix a -> Ix ix a -> Ix ix a)
                   -- ^ how to combine two corresponding indices
              -> IxList ixs a -> IxList ixs a -> IxList ixs a
zipWithIxList _ Nil        Nil        = Nil
zipWithIxList f (x ::: xs) (y ::: ys) = f x y ::: zipWithIxList f xs ys

-- | Force all the 'Ix' values in the list to WHNF.
forceIxList :: forall ixs a . IxList ixs a -> IxList ixs a
forceIxList Nil          = Nil
forceIxList (ix ::: ixs) = ix !::: forceIxList ixs

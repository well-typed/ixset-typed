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
{-# OPTIONS_HADDOCK not-home #-}

{- |

This module defines the 'IxList' type of lists of indices.

= WARNING

This module exposes internal implementation details of @ixset-typed@.  It allows
invariants to be broken via direct access to datatype constructors, and is
subject to change without warning in future releases.

-}
module Data.IxSet.Typed.Internal.IxList
    ( IxList(..)
    , (!:::)
    , All
    , IsIndexOf(..)
    , Indexable(..)
    , project
    , lengthIxList
    , foldlIxList'
    , mapIxList
    , mapIxList'
    , zipWithIxList
    , forceIxList
    , ixList
    , MkIxList(..)
    ) where

import Control.DeepSeq (NFData(..))
import Data.Kind (Type, Constraint)
import Prelude hiding (filter, null)

import Data.IxSet.Typed.Internal.Ix (Ix(Ix))

-- | A term-level list of indices (t'Ix' values), indexed by the type-level list
-- of index types @ixs@ and the element type @a@.
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
-- of type @'Data.IxSet.Typed.IxSet' ixs a@.
--
-- In order to use an 'Data.IxSet.Typed.IxSet' on a particular type, you have to
-- make it an instance of 'Indexable' yourself. There are no
-- predefined instances of 'Indexable'.
--
class (All Ord ixs, Ord a) => Indexable ixs a where

  -- | Define how the indices for this particular type should look like.
  --
  -- Use the 'ixList' function to construct the list of indices, and use
  -- 'Data.IxSet.Typed.ixFun' (or 'Data.IxSet.Typed.ixGen') for individual indices.
  indices :: IxList ixs a

-- | Constraint for membership in the type-level list. Says that @ix@
-- is contained in the index list @ixs@.
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

-- | Project out the indices from a value of an 'Indexable' type.
--
-- @since 0.6
--
project :: forall proxy ixs ix a . (Indexable ixs a, IsIndexOf ix ixs) => proxy ixs -> a -> [ix]
project _ = case access (indices :: IxList ixs a) :: Ix ix a of
              Ix _ f -> f

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

-- | Force all the t'Ix' values in the list to WHNF.
forceIxList :: forall ixs a . IxList ixs a -> IxList ixs a
forceIxList Nil          = Nil
forceIxList (ix ::: ixs) = ix !::: forceIxList ixs


--------------------------------------------------------------------------
-- 'IxList' construction
--------------------------------------------------------------------------

-- | Create an (empty) 'IxList' from a number of indices. Useful in the 'Indexable'
-- 'indices' method. Use 'Data.IxSet.Typed.ixFun' and 'Data.IxSet.Typed.ixGen' for the individual indices.
--
-- Note that this function takes a variable number of arguments.
-- Here are some example types at which the function can be used:
--
-- > ixList :: Ix ix1 a -> IxList '[ix1] a
-- > ixList :: Ix ix1 a -> Ix ix2 a -> IxList '[ix1, ix2] a
-- > ixList :: Ix ix1 a -> Ix ix2 a -> Ix ix3 a -> IxList '[ix1, ix2, ix3] a
-- > ixList :: ...
--
-- Concrete example use:
--
-- > instance Indexable '[..., Index1Type, Index2Type] Type where
-- >     indices = ixList
-- >                 ...
-- >                 (ixFun getIndex1)
-- >                 (ixGen (Proxy :: Proxy Index2Type))
--
ixList :: MkIxList ixs ixs a r => r
ixList = ixList' id

-- | Class that allows a variable number of arguments to be passed to the
-- 'Data.IxSet.Typed.ixSet' and 'Data.IxSet.Typed.mkEmpty' functions. See the
-- documentation of these functions for more information.
class MkIxList ixs ixs' a r | r -> a ixs ixs' where
  ixList' :: (IxList ixs a -> IxList ixs' a) -> r

instance MkIxList '[] ixs a (IxList ixs a) where
  ixList' acc = acc Nil

instance MkIxList ixs ixs' a r => MkIxList (ix ': ixs) ixs' a (Ix ix a -> r) where
  ixList' acc ix = ixList' (\ x -> acc (ix ::: x))

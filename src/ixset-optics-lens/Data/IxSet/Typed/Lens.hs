{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.IxSet.Typed.Lens(
  atPrimaryKey,
  ixPrimaryKey,
  eqKey,
  eqKeys,
  overEqKey,
  asSet
) where

import Control.Lens
import Data.IxSet.Typed as IS
import Data.Set (Set)

type GetIdx ixs ix a = (IS.Indexable ixs a, IS.IsIndexOf ix ixs)

-- | Assuming the given GetIdx is a /primary key/, constructs a lens to access
-- the value associated with the primary key. The getting operation uses 'getEQ'
-- and 'getOne' and the setting operation uses 'updateIx' or 'deleteIx'.
-- Therefore, this /will/ violate lens laws if the given GetIdx is not actually a
-- primary key.
atPrimaryKey :: GetIdx ixs ix a => ix -> Lens' (IxSet ixs a) (Maybe a)
atPrimaryKey i = lens sa sbt
  where
    sa = getOne . getEQ i
    {-# INLINE sa #-}

    sbt s Nothing = deleteIx i s
    sbt s (Just b) = updateIx i b s
    {-# INLINE sbt #-}
{-# INLINE atPrimaryKey #-}

-- | Assuming the given GetIdx is a /primary key/, constructs a traversal to
-- access the value associated with the primary key. This will not work when the
-- provided GetIdx is not actually a primary key.
ixPrimaryKey :: GetIdx ixs ix a => ix -> Traversal' (IxSet ixs a) a
ixPrimaryKey i = atPrimaryKey i . _Just
{-# INLINE ixPrimaryKey #-}

-- | A fold over items at an index
eqKey :: GetIdx ixs ix a => ix -> Fold (IxSet ixs a) a
eqKey = folding . getEQ
{-# INLINE eqKey #-}

-- | A fold over items at indexes
eqKeys :: GetIdx ixs ix a => [ix] -> Fold (IS.IxSet ixs a) a
eqKeys k = folding (IS.@+ k)
{-# INLINE eqKeys #-}

-- | A simple getter for getEQ. Returns a filtered IxSet
overEqKey :: GetIdx ixs ix a => ix -> Getter (IxSet ixs a) (IxSet ixs a)
overEqKey = to . getEQ
{-# INLINE overEqKey #-}

-- | Turn an IxSet into a Set
asSet :: Getter (IxSet ixs a) (Set a)
asSet = to toSet
{-# INLINE asSet #-}


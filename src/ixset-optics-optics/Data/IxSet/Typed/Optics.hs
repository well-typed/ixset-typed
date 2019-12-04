{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.IxSet.Typed.Optics where

import Control.Applicative
import Data.IxSet.Typed as IS
import qualified Data.Set as Set
import Optics

type GetIdx ixs ix a = (Indexable ixs a, IsIndexOf ix ixs)

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
ixPrimaryKey :: GetIdx ixs ix a => ix -> AffineTraversal' (IS.IxSet ixs a) a
ixPrimaryKey k = atPrimaryKey k % _Just
{-# INLINE ixPrimaryKey #-}

traverseWith :: Indexable ixs a => (IxSet ixs a -> IxSet ixs a) -> Traversal' (IxSet ixs a) a
traverseWith ixsFilter = traversalVL $ \f ixs -> let sa = ixsFilter ixs in foldr (liftA2 IS.insert . f) (pure $ IS.difference ixs sa) sa
{-# INLINE traverseWith #-}

-- | A traversal over items at an idx
-- It is only a valid traversal if the Eq instance of 'a' is a good citizen, particularly that it expresses substitutivity.
ixKey :: GetIdx ixs ix a => ix -> Traversal' (IxSet ixs a) a
ixKey = traverseWith . getEQ
{-# INLINE ixKey #-}

-- | A traversal over items at indexes
-- It is only a valid traversal if the Eq instance of 'a' is a good citizen, particularly that it expresses substitutivity.
ixKeys :: GetIdx ixs ix a => [ix] -> Traversal' (IS.IxSet ixs a) a
ixKeys = traverseWith . flip (IS.@+)
{-# INLINE ixKeys #-}

-- | Get or set the contained IxSet at a given index.
atKey :: GetIdx ixs ix a => ix -> Lens' (IS.IxSet ixs a) (IS.IxSet ixs a)
atKey k = lens (getEQ k) (\ixs b -> IS.union b $ IS.difference ixs (getEQ k ixs))
{-# INLINE atKey #-}

-- | Isomorphism from IxSet to Set
asSet :: Indexable ixs a => Iso' (IxSet ixs a) (Set.Set a)
asSet = iso toSet fromSet
{-# INLINE asSet #-}

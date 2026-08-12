{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Sample data type and index declarations used by the benchmarks.
--
module Bench.Types
  ( -- * Element type
    Entry(..)
  , EntryId(..)
  , Author(..)
  , Updated(..)
  , Tag(..)
  , Priority(..)
  , GenEntry(..)
    -- * Index sets
  , EntryIxs
  , Entries
  , Entries1
  , Entries2
  , Entries3
  , SmallEntries
  , GenEntries
    -- * Deterministic test data
  , mkEntries
  , mkEntriesFrom
  , mkEntry
  , primaryTag
  ) where

import Control.DeepSeq (NFData(..))
import Data.Data       (Data)
import Data.Proxy      (Proxy(..))
import Data.IxSet.Typed

newtype EntryId  = EntryId Int     deriving (Eq, Ord, Show, Data)
newtype Author   = Author String   deriving (Eq, Ord, Show, Data)
newtype Updated  = Updated Int     deriving (Eq, Ord, Show, Data)
newtype Tag      = Tag String      deriving (Eq, Ord, Show, Data)
newtype Priority = Priority Int    deriving (Eq, Ord, Show, Data)

-- The @Entry@ type is indexed on five keys with deliberately different
-- characteristics:
--
--   * 'EntryId' is unique (one element per key),
--   * 'Author' has moderate cardinality,
--   * 'Updated' has high cardinality and is queried with ranges,
--   * 'Tag' is multi-valued (each element occurs under several keys),
--   * 'Priority' has very low cardinality (few keys, huge buckets).
--
data Entry = Entry
  { eId       :: EntryId
  , eAuthor   :: Author
  , eUpdated  :: Updated
  , eTags     :: [Tag]
  , ePriority :: Priority
  }
  deriving (Eq, Ord, Show, Data)

-- | Same payload as 'Entry', but indexed via 'ixGen' rather than 'ixFun',
-- so that the cost of the SYB-based index extraction can be compared.
newtype GenEntry = GenEntry Entry
  deriving (Eq, Ord, Show, Data)

instance NFData EntryId  where rnf (EntryId i)  = rnf i
instance NFData Author   where rnf (Author s)   = rnf s
instance NFData Updated  where rnf (Updated i)  = rnf i
instance NFData Tag      where rnf (Tag s)      = rnf s
instance NFData Priority where rnf (Priority i) = rnf i

instance NFData Entry where
  rnf (Entry i a u ts p) = rnf i `seq` rnf a `seq` rnf u `seq` rnf ts `seq` rnf p

instance NFData GenEntry where
  rnf (GenEntry e) = rnf e

type EntryIxs = '[EntryId, Author, Updated, Tag, Priority]
type Entries  = IxSet EntryIxs Entry

instance Indexable EntryIxs Entry where
  indices = ixList
              (ixFun (\ e -> [eId e]))
              (ixFun (\ e -> [eAuthor e]))
              (ixFun (\ e -> [eUpdated e]))
              (ixFun eTags)
              (ixFun (\ e -> [ePriority e]))

-- | Prefixes of 'EntryIxs', for measuring how the cost of the various
-- operations scales with the number of declared indices.
type Entries1 = IxSet '[EntryId] Entry
type Entries2 = IxSet '[EntryId, Author] Entry
type Entries3 = IxSet '[EntryId, Author, Updated] Entry

instance Indexable '[EntryId] Entry where
  indices = ixList (ixFun (\ e -> [eId e]))

instance Indexable '[EntryId, Author] Entry where
  indices = ixList
              (ixFun (\ e -> [eId e]))
              (ixFun (\ e -> [eAuthor e]))

instance Indexable '[EntryId, Author, Updated] Entry where
  indices = ixList
              (ixFun (\ e -> [eId e]))
              (ixFun (\ e -> [eAuthor e]))
              (ixFun (\ e -> [eUpdated e]))

-- | Two indices declared with 'ixFun', to be compared against 'GenEntries'.
type SmallEntries = IxSet '[Author, Priority] Entry

instance Indexable '[Author, Priority] Entry where
  indices = ixList
              (ixFun (\ e -> [eAuthor e]))
              (ixFun (\ e -> [ePriority e]))

-- | The same two indices declared with 'ixGen'.
type GenEntries = IxSet '[Author, Priority] GenEntry

instance Indexable '[Author, Priority] GenEntry where
  indices = ixList
              (ixGen (Proxy :: Proxy Author))
              (ixGen (Proxy :: Proxy Priority))

--------------------------------------------------------------------------
-- Deterministic test data
--------------------------------------------------------------------------

-- | A cheap linear congruential generator. Benchmark data is generated
-- from a fixed seed so that runs are comparable across machines, without
-- depending on the @random@ package.
lcgs :: Int -> [Int]
lcgs = drop 1 . iterate step
  where
    step s = (s * 1103515245 + 12345) `mod` 2147483648

-- | @mkEntries n@ produces @n@ entries with distinct 'EntryId's, and
-- pseudo-random values for all other fields.
mkEntries :: Int -> [Entry]
mkEntries = mkEntriesFrom 0

-- | As 'mkEntries', but with 'EntryId's starting at the given offset.
-- Two calls with disjoint offsets produce disjoint sets of entries.
mkEntriesFrom :: Int -> Int -> [Entry]
mkEntriesFrom offset n =
    zipWith mkEntry [offset .. offset + n - 1] (lcgs (offset + 1))

-- | @mkEntry i r@ is the entry with 'EntryId' @i@, with its remaining
-- fields derived from the seed @r@.
mkEntry :: Int -> Int -> Entry
mkEntry i r = Entry
  { eId       = EntryId i
  , eAuthor   = Author ("author-" ++ show (r `mod` 64))
  , eUpdated  = Updated ((r `div` 64) `mod` 100000)
    -- Multi-valued index: three tags per entry, occasionally coinciding.
  , eTags     = [ Tag ("tag-" ++ show ((r `div` k) `mod` 256)) | k <- [1, 11, 101] ]
  , ePriority = Priority (r `mod` 5)
  }

-- | The first tag of an entry. Entries built by 'mkEntry' always have some.
primaryTag :: Entry -> Tag
primaryTag e = case eTags e of
                 t : _ -> t
                 []    -> Tag "tag-0"

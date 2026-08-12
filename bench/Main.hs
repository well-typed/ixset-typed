{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | Benchmarks for @ixset-typed@.
--
-- Run with:
--
-- > cabal bench
--
-- and, to compare against a previous run:
--
-- > cabal bench --benchmark-options='--csv before.csv'
-- > ... apply patch ...
-- > cabal bench --benchmark-options='--baseline before.csv'
--
-- Both 'nf' and 'whnf' results are reported, because an 'IxSet' is spine-strict
-- in some places and lazy in others, so how much of the result of an operation
-- is demanded matters significantly. For an operation that is already strict,
-- the 'nf' measurement is simply the 'whnf' one plus a traversal of the result,
-- so the absolute size of the difference is not interesting in itself.  Rather,
-- it is useful to compare /changes/ in the difference between runs.
--
-- Allocation figures reported alongside the timings (the suite is built with
-- @-with-rtsopts=-T@) and are usually more useful than wall-clock time as they
-- are less subject to noise.
--
module Main (main) where

import           Control.DeepSeq      (NFData(..), force)
import           Control.Exception    (evaluate)
import qualified Data.List            as List
import           Data.Proxy           (Proxy(..))
import           Data.Set             (Set)
import qualified Data.Set             as Set
import           GHC.Generics         (Generic)

import           Data.IxSet.Typed     ((@=), (@<), (@>=), (@>=<=), (@+), (@*), (&&&), (|||), (\\\))
import qualified Data.IxSet.Typed     as IxSet
import           Test.Tasty.Bench
    ( bench,
      bgroup,
      defaultMain,
      env,
      nf,
      whnf,
      Benchmark,
      Benchmarkable
    )

import           Bench.Types

main :: IO ()
main = defaultMain [ benchmarks n | n <- sizes ]

-- | Element counts at which the whole suite is run.
sizes :: [Int]
sizes = [1000, 10000]

--------------------------------------------------------------------------
-- Forcing
--------------------------------------------------------------------------

-- | How much of the result of an operation to force. This is 'whnf' or
-- 'nf', abstracted over so that each benchmark can be run at both.
type Forcer = forall a b. NFData b => (a -> b) -> a -> Benchmarkable

-- | Run a group of benchmarks once per 'Forcer'.
byForcing :: String -> (Forcer -> [(String, Benchmarkable)]) -> Benchmark
byForcing name benches =
  bgroup name
    [ bgroup "whnf" (map (uncurry bench) (benches whnf))
    , bgroup "nf"   (map (uncurry bench) (benches nf))
    ]

--------------------------------------------------------------------------
-- Fixtures
--------------------------------------------------------------------------

-- | Everything a benchmark group needs, generated (and forced) once per
-- size by 'env', so that data generation is not measured.
data Fixture = Fixture
  { fxSize       :: Int
  , fxEntries    :: [Entry]
  , fxGenEntries :: [GenEntry]
  , fxIxSet      :: Entries
  , fxIxSet1     :: Entries1
  , fxIxSet2     :: Entries2
  , fxIxSet3     :: Entries3
  , fxIxSetB     :: Entries    -- ^ overlaps 'fxIxSet' in half its elements
  , fxSet        :: Set Entry
  , fxMember     :: Entry      -- ^ an element of 'fxIxSet'
  , fxFresh      :: Entry      -- ^ not an element of 'fxIxSet'
  , fxId         :: EntryId
  , fxAuthor     :: Author
  , fxTag        :: Tag
  , fxTags       :: [Tag]
  , fxPriority   :: Priority
  , fxLo         :: Updated
  , fxHi         :: Updated
    -- | Subsets to be removed in bulk, scattered across the indices
    -- rather than contiguous in any one of them.
  , fxDeleteOne  :: Set Entry
  , fxDeleteFew  :: Set Entry  -- ^ a tenth of the elements
  , fxDeleteHalf :: Set Entry  -- ^ half of the elements
  , fxDeleteList :: [Entry]    -- ^ 'fxDeleteFew' as a list
  , fxIxSetFew   :: Entries    -- ^ 'fxDeleteFew' as an 'IxSet'
  }
  deriving Generic

instance NFData Fixture

mkFixture :: Int -> Fixture
mkFixture n = Fixture
  { fxSize       = n
  , fxEntries    = entries
  , fxGenEntries = map GenEntry entries
  , fxIxSet      = ixs
  , fxIxSet1     = IxSet.fromList entries
  , fxIxSet2     = IxSet.fromList entries
  , fxIxSet3     = IxSet.fromList entries
  , fxIxSetB     = IxSet.fromList (drop half entries ++ mkEntriesFrom n half)
  , fxSet        = Set.fromList entries
  , fxMember     = member
  , fxFresh      = mkEntry (2 * n) (2 * n)
  , fxId         = eId member
  , fxAuthor     = eAuthor member
  , fxTag        = primaryTag member
  , fxTags       = take 3 tagKeys
  , fxPriority   = ePriority member
  , fxLo         = updKeys !! (length updKeys `div` 4)
  , fxHi         = updKeys !! (3 * length updKeys `div` 4)
  , fxDeleteOne  = Set.singleton member
  , fxDeleteFew  = Set.fromList few
  , fxDeleteHalf = Set.fromList (everyNth 2 entries)
  , fxDeleteList = few
  , fxIxSetFew   = IxSet.fromList few
  }
  where
    half    = n `div` 2
    entries = mkEntries n
    few     = everyNth 10 entries
    ixs     = IxSet.fromList entries :: Entries
    member  = entries !! half
    tagKeys = IxSet.indexKeys ixs :: [Tag]
    updKeys = IxSet.indexKeys ixs :: [Updated]

-- | Every @k@th element, so that a selection is spread over all of the
-- indices instead of being contiguous in any one of them.
everyNth :: Int -> [a] -> [a]
everyNth k xs = [ x | (i, x) <- zip [0 :: Int ..] xs, i `mod` k == 0 ]

--------------------------------------------------------------------------
-- The benchmarks
--------------------------------------------------------------------------

benchmarks :: Int -> Benchmark
benchmarks n =
  env (evaluate (force (mkFixture n))) $ \ fx ->
    bgroup (show n ++ " elements")
      [ byForcing "construction"   (construction fx)
      , byForcing "update"         (update fx)
      , byForcing "bulk delete"    (bulkDelete fx)
      , byForcing "query"          (query fx)
      , byForcing "set operations" (setOperations fx)
      , byForcing "conversion"     (conversion fx)
      , byForcing "index count"    (indexCount fx)
      , byForcing "ixFun vs ixGen" (indexKind fx)
      ]

-- | Building an 'IxSet' from scratch, i.e. the price of the indices.
construction :: Fixture -> Forcer -> [(String, Benchmarkable)]
construction fx forcer =
  [ ("fromList",           forcer (IxSet.fromList :: [Entry] -> Entries) es)
  , ("fromSet",            forcer (IxSet.fromSet :: Set Entry -> Entries) (fxSet fx))
  , ("insertList",         forcer (\ xs -> IxSet.insertList xs IxSet.empty :: Entries) es)
  , ("repeated insert",    forcer (List.foldl' (flip IxSet.insert) (IxSet.empty :: Entries)) es)
  , ("Set.fromList (ref)", forcer Set.fromList es)
  ]
  where
    es = fxEntries fx

-- | Incremental modification of an existing 'IxSet'.
update :: Fixture -> Forcer -> [(String, Benchmarkable)]
update fx forcer =
  [ ("insert (new element)",      forcer (\ e -> IxSet.insert e ixs) (fxFresh fx))
  , ("insert (existing element)", forcer (\ e -> IxSet.insert e ixs) (fxMember fx))
  , ("delete",                    forcer (\ e -> IxSet.delete e ixs) (fxMember fx))
  , ("delete (absent element)",   forcer (\ e -> IxSet.delete e ixs) (fxFresh fx))
  , ("updateIx",                  forcer (\ i -> IxSet.updateIx i (fxFresh fx) ixs) (fxId fx))
  , ("deleteIx",                  forcer (\ i -> IxSet.deleteIx i ixs) (fxId fx))
  , ("Set.insert (ref)",          forcer (\ e -> Set.insert e (fxSet fx)) (fxFresh fx))
  ]
  where
    ixs = fxIxSet fx

-- | Bulk removal. 'IxSet.deleteSet', 'IxSet.difference' and
-- 'IxSet.filter' all work through the indices of the part being removed,
-- instead of deleting element by element; the repeated 'IxSet.delete'
-- benchmark is the baseline they are meant to improve on, and the
-- selectivity sweep shows what each of them costs as a function of how
-- much is removed.
--
-- Note that 'IxSet.filter' is defined by removing the complement of the
-- predicate, so it is the elements it /discards/, not the ones it keeps,
-- that determine its cost.
bulkDelete :: Fixture -> Forcer -> [(String, Benchmarkable)]
bulkDelete fx forcer =
  [ ("deleteSet (1 element)",     forcer (\ s -> IxSet.deleteSet s ixs) (fxDeleteOne fx))
  , ("deleteSet (10%)",           forcer (\ s -> IxSet.deleteSet s ixs) (fxDeleteFew fx))
  , ("deleteSet (50%)",           forcer (\ s -> IxSet.deleteSet s ixs) (fxDeleteHalf fx))
  , ("deleteSet (all)",           forcer (\ s -> IxSet.deleteSet s ixs) (fxSet fx))
  , ("repeated delete (10%)",     forcer (List.foldl' (flip IxSet.delete) ixs) (fxDeleteList fx))
  , ("difference (10%)",          forcer (IxSet.difference ixs) (fxIxSetFew fx))
  , ("filter (keep all)",         forcer (\ p -> IxSet.filter p ixs) (const True))
  , ("filter (keep 90%)",         forcer (\ p -> IxSet.filter p ixs) keep90)
  , ("filter (keep 50%)",         forcer (\ p -> IxSet.filter p ixs) keep50)
  , ("filter (keep none)",        forcer (\ p -> IxSet.filter p ixs) (const False))
  , ("Set.filter (ref, keep 50%)", forcer (\ p -> Set.filter p (fxSet fx)) keep50)
  ]
  where
    ixs    = fxIxSet fx
    -- The ids run from 0, so a threshold on the id keeps a known fraction.
    keep90 = \ e -> eId e >= EntryId (fxSize fx `div` 10)
    keep50 = \ e -> eId e >= EntryId (fxSize fx `div` 2)

-- | Queries. These are currently lazy in the indices of their result, so
-- the gap between the two forcings is at its widest here: WHNF computes
-- the element set only, NF additionally rebuilds every index of the
-- result.
query :: Fixture -> Forcer -> [(String, Benchmarkable)]
query fx forcer =
  [ ("getEQ (unique key)",         forcer (\ s -> s @= fxId fx) ixs)
  , ("getEQ (medium cardinality)", forcer (\ s -> s @= fxAuthor fx) ixs)
  , ("getEQ (low cardinality)",    forcer (\ s -> s @= fxPriority fx) ixs)
  , ("getEQ (multi-valued index)", forcer (\ s -> s @= fxTag fx) ixs)
  , ("getLT",                      forcer (\ s -> s @< fxHi fx) ixs)
  , ("getGTE",                     forcer (\ s -> s @>= fxLo fx) ixs)
  , ("getRange (@>=<=)",           forcer (\ s -> s @>=<= (fxLo fx, fxHi fx)) ixs)
  , ("union of keys (@+)",         forcer (\ s -> s @+ fxTags fx) ixs)
  , ("intersection of keys (@*)",  forcer (\ s -> s @* fxTags fx) ixs)
  , ("chained (@= then range)",    forcer (\ s -> s @= fxAuthor fx @>=<= (fxLo fx, fxHi fx)) ixs)
  , ("chained (three keys)",       forcer (\ s -> s @= fxAuthor fx @= fxPriority fx @= fxTag fx) ixs)
  , ("Set.filter (ref, unique key)",
      forcer (\ i -> Set.filter ((== i) . eId) set) (fxId fx))
  , ("Set.filter (ref, low cardinality key)",
      forcer (\ p -> Set.filter ((== p) . ePriority) set) (fxPriority fx))
  , ("Set.filter (ref, range)",
      forcer (\ (lo, hi) -> Set.filter (\ e -> eUpdated e >= lo && eUpdated e <= hi) set)
            (fxLo fx, fxHi fx))
  ]
  where
    ixs = fxIxSet fx
    set = fxSet fx

-- | 'IxSet.union', 'IxSet.intersection' and 'IxSet.difference' operate on
-- the indices directly, rather than rebuilding them from the elements.
-- Both arguments here are of the same size, overlapping in half of their
-- elements.
setOperations :: Fixture -> Forcer -> [(String, Benchmarkable)]
setOperations fx forcer =
  [ ("union",                   forcer (IxSet.union ixs) ixs')
  , ("intersection",            forcer (IxSet.intersection ixs) ixs')
  , ("difference",              forcer (IxSet.difference ixs) ixs')
  , ("(|||)",                   forcer (ixs |||) ixs')
  , ("(&&&)",                   forcer (ixs &&&) ixs')
  , ("(\\\\\\)",                   forcer (ixs \\\) ixs')
  , ("Set.union (ref)",         forcer (Set.union (fxSet fx)) (IxSet.toSet ixs'))
  , ("Set.intersection (ref)",  forcer (Set.intersection (fxSet fx)) (IxSet.toSet ixs'))
  , ("Set.difference (ref)",    forcer (Set.difference (fxSet fx)) (IxSet.toSet ixs'))
  ]
  where
    ixs  = fxIxSet fx
    ixs' = fxIxSetB fx

-- | Getting data back out again.
conversion :: Fixture -> Forcer -> [(String, Benchmarkable)]
conversion fx forcer =
  [ ("toList",      forcer IxSet.toList ixs)
  , ("toSet",       forcer IxSet.toSet ixs)
  , ("toAscList",   forcer (IxSet.toAscList (Proxy :: Proxy Updated)) ixs)
  , ("toDescList",  forcer (IxSet.toDescList (Proxy :: Proxy Updated)) ixs)
  , ("groupBy",     forcer (\ s -> IxSet.groupBy s :: [(Author, [Entry])]) ixs)
  , ("groupAscBy",  forcer (\ s -> IxSet.groupAscBy s :: [(Author, [Entry])]) ixs)
  , ("groupDescBy", forcer (\ s -> IxSet.groupDescBy s :: [(Author, [Entry])]) ixs)
  , ("indexKeys",   forcer (\ s -> IxSet.indexKeys s :: [Updated]) ixs)
  , ("getOne",      forcer (\ i -> IxSet.getOne (ixs @= i)) (fxId fx))
  , ("size",        forcer IxSet.size ixs)
  , ("null",        forcer IxSet.null ixs)
  , ("stats",       forcer IxSet.stats ixs)
  ]
  where
    ixs = fxIxSet fx

-- | How the cost of construction and of a single update scales with the
-- number of declared indices.
indexCount :: Fixture -> Forcer -> [(String, Benchmarkable)]
indexCount fx forcer =
  [ ("fromList (1 index)",   forcer (IxSet.fromList :: [Entry] -> Entries1) es)
  , ("fromList (2 indices)", forcer (IxSet.fromList :: [Entry] -> Entries2) es)
  , ("fromList (3 indices)", forcer (IxSet.fromList :: [Entry] -> Entries3) es)
  , ("fromList (5 indices)", forcer (IxSet.fromList :: [Entry] -> Entries) es)
  , ("insert (1 index)",     forcer (\ e -> IxSet.insert e (fxIxSet1 fx)) fresh)
  , ("insert (2 indices)",   forcer (\ e -> IxSet.insert e (fxIxSet2 fx)) fresh)
  , ("insert (3 indices)",   forcer (\ e -> IxSet.insert e (fxIxSet3 fx)) fresh)
  , ("insert (5 indices)",   forcer (\ e -> IxSet.insert e (fxIxSet fx)) fresh)
  , ("getEQ (1 index)",      forcer (\ i -> fxIxSet1 fx @= i) (fxId fx))
  , ("getEQ (2 indices)",    forcer (\ i -> fxIxSet2 fx @= i) (fxId fx))
  , ("getEQ (3 indices)",    forcer (\ i -> fxIxSet3 fx @= i) (fxId fx))
  , ("getEQ (5 indices)",    forcer (\ i -> fxIxSet fx @= i) (fxId fx))
  ]
  where
    es    = fxEntries fx
    fresh = fxFresh fx

-- | 'ixGen' uses an SYB traversal to extract keys, 'ixFun' a supplied
-- function. Same data, same two indices, so this measures the difference
-- between the two ways of declaring them.
indexKind :: Fixture -> Forcer -> [(String, Benchmarkable)]
indexKind fx forcer =
  [ ("ixFun", forcer (IxSet.fromList :: [Entry] -> SmallEntries) (fxEntries fx))
  , ("ixGen", forcer (IxSet.fromList :: [GenEntry] -> GenEntries) (fxGenEntries fx))
  ]

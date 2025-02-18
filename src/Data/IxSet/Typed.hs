{-# LANGUAGE UndecidableInstances, FlexibleInstances,
             MultiParamTypeClasses, TemplateHaskell, RankNTypes,
             FunctionalDependencies, DeriveDataTypeable,
             GADTs, CPP, ScopedTypeVariables, KindSignatures,
             DataKinds, TypeOperators, StandaloneDeriving,
             TypeFamilies, ScopedTypeVariables, ConstraintKinds,
             FunctionalDependencies, FlexibleContexts, BangPatterns #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{- |
An efficient implementation of queryable sets.

Assume you have a family of types such as:

> data Entry      = Entry Author [Author] Updated Id Content
>   deriving (Show, Eq, Ord, Data, Typeable)
> newtype Updated = Updated UTCTime
>   deriving (Show, Eq, Ord, Data, Typeable)
> newtype Id      = Id Int64
>   deriving (Show, Eq, Ord, Data, Typeable)
> newtype Content = Content String
>   deriving (Show, Eq, Ord, Data, Typeable)
> newtype Author  = Author Email
>   deriving (Show, Eq, Ord, Data, Typeable)
> type Email      = String
> data Test = Test
>   deriving (Show, Eq, Ord, Data, Typeable)

1. Decide what parts of your type you want indexed and make your type
an instance of 'Indexable'. Use 'ixFun' and 'ixGen' to build indices:

    > type EntryIxs = '[Author, Id, Updated, Test]
    > type IxEntry  = IxSet EntryIxs Entry
    >
    > instance Indexable EntryIxs Entry where
    >   indices = ixList
    >               (ixGen (Proxy :: Proxy Author))        -- out of order
    >               (ixGen (Proxy :: Proxy Id))
    >               (ixGen (Proxy :: Proxy Updated))
    >               (ixGen (Proxy :: Proxy Test))          -- bogus index

    The use of 'ixGen' requires the 'Data' and 'Typeable' instances above.
    You can build indices manually using 'ixFun'. You can also use the
    Template Haskell function 'inferIxSet' to generate an 'Indexable'
    instance automatically.

2. Use 'insert', 'insertList', 'delete', 'updateIx', 'deleteIx'
and 'empty' to build up an 'IxSet' collection:

    > entries  = insertList [e1, e2, e3, e4] (empty :: IxEntry)
    > entries1 = foldr delete entries [e1, e3]
    > entries2 = updateIx (Id 4) e5 entries

3. Use the query functions below to grab data from it:

    > entries @= Author "john@doe.com" @< Updated t1

    Statement above will find all items in entries updated earlier than
    @t1@ by @john\@doe.com@.

4. Text index

    If you want to do add a text index create a calculated index.  Then if you want
    all entries with either @word1@ or @word2@, you change the instance
    to:

    > newtype Word = Word String
    >   deriving (Show, Eq, Ord)
    >
    > getWords (Entry _ _ _ _ (Content s)) = map Word $ words s
    >
    > type EntryIxs = '[..., Word]
    > instance Indexable EntryIxs Entry where
    >     indices = ixList
    >                 ...
    >                 (ixFun getWords)

    Now you can do this query to find entries with any of the words:

    > entries @+ [Word "word1", Word "word2"]

    And if you want all entries with both:

    > entries @* [Word "word1", Word "word2"]

5. Find only the first author

    If an @Entry@ has multiple authors and you want to be able to query on
    the first author only, define a @FirstAuthor@ datatype and create an
    index with this type.  Now you can do:

    > newtype FirstAuthor = FirstAuthor Email
    >   deriving (Show, Eq, Ord)
    >
    > getFirstAuthor (Entry author _ _ _ _) = [FirstAuthor author]
    >
    > type EntryIxs = '[..., FirstAuthor]
    > instance Indexable EntryIxs Entry where
    >     indices = ixList
    >                 ...
    >                 (ixFun getFirstAuthor)

    > entries @= (FirstAuthor "john@doe.com")  -- guess what this does

-}

module Data.IxSet.Typed
    (
     -- * Set type
     IxSet(),
     IxList(),
     Indexable(..),
     IsIndexOf(),
     All,
     -- ** Declaring indices
     Ix(),
     ixList,
     MkIxList(),
     ixFun,
     ixGen,
     -- ** TH derivation of indices
     noCalcs,
     inferIxSet,

     -- * Changes to set
     IndexOp,
     SetOp,
     change,
     insert,
     insertList,
     delete,
     deleteSet,
     filter,
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
     groupBy,
     groupAscBy,
     groupDescBy,
     indexKeys,

     -- * Index creation helpers
     flatten,
     flattenWithCalcs,

     -- * Debugging and optimization
     stats
)
where

import Data.Kind
import Prelude hiding (filter, null)

import           Control.Arrow  (first, second)
import           Control.DeepSeq
import qualified Data.Foldable  as Fold
import           Data.Generics  (Data, gmapQ)
-- import qualified Data.Generics.SYB.WithClass.Basics as SYBWC
import qualified Data.IxSet.Typed.Ix  as Ix
import           Data.IxSet.Typed.Ix  (Ix(Ix))
import qualified Data.List      as List
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Maybe     (fromMaybe)
import           Data.SafeCopy  (SafeCopy(..), contain, safeGet, safePut)
import           Data.Semigroup (Semigroup(..))
import           Data.Set       (Set)
import qualified Data.Set       as Set
import           Data.Typeable  (Typeable, cast {- , typeOf -})
import Language.Haskell.TH      as TH hiding (Type)

--------------------------------------------------------------------------
-- The main 'IxSet' datatype.
--------------------------------------------------------------------------

-- | Set with associated indices.
--
-- The type-level list 'ixs' contains all types that are valid index keys.
-- The type 'a' is the type of elements in the indexed set.
--
-- On strictness: An 'IxSet' is "mostly" spine-strict. It is generally
-- spine-strict in the set itself. All operations on 'IxSet' with the
-- exception of queries are spine-strict in the indices as well. Query
-- operations, however, are lazy in the indices, so querying a number of
-- times and subsequently selecting the result will not unnecessarily
-- rebuild all indices.
--
data IxSet (ixs :: [Type]) (a :: Type) where
  IxSet :: !(Set a) -> !(IxList ixs a) -> IxSet ixs a

data IxList (ixs :: [Type]) (a :: Type) where
  Nil   :: IxList '[] a
  (:::) :: Ix ix a -> IxList ixs a -> IxList (ix ': ixs) a

infixr 5 :::

-- | A strict variant of ':::'.
(!:::) :: Ix ix a -> IxList ixs a -> IxList (ix ': ixs) a
(!:::) !ix !ixs = ix ::: ixs

infixr 5 !:::

-- TODO:
--
-- We cannot currently derive Typeable for 'IxSet':
--
--   * In ghc-7.6, Typeable isn't supported for non-* kinds.
--   * In ghc-7.8, see bug #8950. We can work around this, but I rather
--     would wait for a proper fix.

-- deriving instance Data (IxSet ixs a)
-- deriving instance Typeable IxSet


--------------------------------------------------------------------------
-- Type-level tools for dealing with indexed sets.
--
-- These are partially internal. TODO: Move to different module?
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
type family All (c :: Type -> Constraint) (xs :: [Type]) :: Constraint
type instance All c '[]       = ()
type instance All c (x ': xs) = (c x, All c xs)

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
lengthIxList = go 0
  where
    go :: forall ixs'. Int -> IxList ixs' a -> Int
    go !acc Nil        = acc
    go !acc (_ ::: xs) = go (acc + 1) xs

-- | Turn an index list into a normal list, given a function that
-- turns an arbitrary index into an element of a fixed type @r@.
ixListToList :: All Ord ixs
             => (forall ix. Ord ix => Ix ix a -> r)
                  -- ^ what to do with each index
             -> IxList ixs a -> [r]
ixListToList _ Nil        = []
ixListToList f (x ::: xs) = f x : ixListToList f xs

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

-- | Zip two index lists of compatible type (spine-strict).
zipWithIxList' :: All Ord ixs
               => (forall ix. Ord ix => Ix ix a -> Ix ix a -> Ix ix a)
                    -- ^ how to combine two corresponding indices
               -> IxList ixs a -> IxList ixs a -> IxList ixs a
zipWithIxList' _ Nil        Nil        = Nil
zipWithIxList' f (x ::: xs) (y ::: ys) = f x y !::: zipWithIxList' f xs ys
#if __GLASGOW_HASKELL__ < 800
zipWithIxList' _ _          _          = error "Data.IxSet.Typed.zipWithIxList: impossible"
  -- the line above is actually impossible by the types; it's just there
  -- to please avoid the warning resulting from the exhaustiveness check
#endif

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

instance (All NFData ixs, NFData a) => NFData (IxList ixs a) where
  rnf Nil        = ()
  rnf (x ::: xs) = rnf x `seq` rnf xs

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

-- TODO: Do we need SYBWC?
{-
instance ( SYBWC.Data ctx a
         , SYBWC.Data ctx [a]
         , SYBWC.Sat (ctx (IxSet a))
         , SYBWC.Sat (ctx [a])
         , Indexable a
         , Data a
         , Ord a
         )
       => SYBWC.Data ctx (IxSet a) where
    gfoldl _ f z ixset  = z fromList `f` toList ixset
    toConstr _ (IxSet _) = ixSetConstr
    gunfold _ k z c  = case SYBWC.constrIndex c of
                       1 -> k (z fromList)
                       _ -> error "IxSet.SYBWC.Data.gunfold unexpected match"
    dataTypeOf _ _ = ixSetDataType

ixSetConstr :: SYBWC.Constr
ixSetConstr = SYBWC.mkConstr ixSetDataType "IxSet" [] SYBWC.Prefix
ixSetDataType :: SYBWC.DataType
ixSetDataType = SYBWC.mkDataType "IxSet" [ixSetConstr]
-}

-- TODO: Do we need Default?
{- FIXME
instance (Indexable a, Ord a,Data a, Default a) => Default (IxSet a) where
    defaultValue = empty
-}

--------------------------------------------------------------------------
-- 'IxSet' construction
--------------------------------------------------------------------------

-- | An empty 'IxSet'.
empty :: Indexable ixs a => IxSet ixs a
empty = IxSet Set.empty indices

-- | Create an (empty) 'IxList' from a number of indices. Useful in the 'Indexable'
-- 'indices' method. Use 'ixFun' and 'ixGen' for the individual indices.
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
-- 'ixSet' and 'mkEmpty' functions. See the documentation of these functions
-- for more information.
class MkIxList ixs ixs' a r | r -> a ixs ixs' where
  ixList' :: (IxList ixs a -> IxList ixs' a) -> r

instance MkIxList '[] ixs a (IxList ixs a) where
  ixList' acc = acc Nil

instance MkIxList ixs ixs' a r => MkIxList (ix ': ixs) ixs' a (Ix ix a -> r) where
  ixList' acc ix = ixList' (\ x -> acc (ix ::: x))

-- | Create a functional index. Provided function should return a list
-- of indices where the value should be found.
--
-- > getIndices :: Type -> [IndexType]
-- > getIndices value = [...indices...]
--
-- > instance Indexable '[IndexType] Type where
-- >     indices = ixList (ixFun getIndices)
--
-- This is the recommended way to create indices.
--
ixFun :: Ord ix => (a -> [ix]) -> Ix ix a
ixFun = Ix Map.empty

-- | Create a generic index. Provided example is used only as type source
-- so you may use a 'Proxy'. This uses flatten to traverse values using
-- their 'Data' instances.
--
-- > instance Indexable '[IndexType] Type where
-- >     indices = ixList (ixGen (Proxy :: Proxy Type))
--
-- In production systems consider using 'ixFun' in place of 'ixGen' as
-- the former one is much faster.
--
ixGen :: forall proxy a ix. (Ord ix, Data a, Typeable ix) => proxy ix -> Ix ix a
ixGen _proxy = ixFun (flatten :: a -> [ix])

--------------------------------------------------------------------------
-- 'IxSet' construction via Template Haskell
--------------------------------------------------------------------------

-- | Function to be used as third argument in 'inferIxSet'
-- when you don't want any calculated values.
noCalcs :: t -> ()
noCalcs _ = ()

-- | Template Haskell helper function for automatically building an
-- 'Indexable' instance from a data type, e.g.
--
-- > data Foo = Foo Int String
-- >   deriving (Eq, Ord, Data, Typeable)
--
-- and
--
-- > inferIxSet "FooDB" ''Foo 'noCalcs [''Int, ''String]
--
-- will define:
--
-- > type FooDB = IxSet '[Int, String] Foo
-- > instance Indexable '[Int, String] Foo where
-- >   ...
--
-- with @Int@ and @String@ as indices defined via
--
-- >   ixFun (flattenWithCalcs noCalcs)
--
-- each.
--
-- /WARNING/: This function uses 'flattenWithCalcs' for index generation,
-- which in turn uses an SYB type-based traversal. It is often more efficient
-- (and sometimes more correct) to explicitly define the indices using
-- 'ixFun'.
--
inferIxSet :: String -> TH.Name -> TH.Name -> [TH.Name] -> Q [Dec]
inferIxSet _ _ _ [] = error "inferIxSet needs at least one index"
inferIxSet ixset typeName calName entryPoints
    = do calInfo <- reify calName
         typeInfo <- reify typeName
         let (context,binders) = case typeInfo of
#if MIN_VERSION_template_haskell(2,11,0)
                                 TyConI (DataD ctxt _ nms _ _ _) -> (ctxt,nms)
                                 TyConI (NewtypeD ctxt _ nms _ _ _) -> (ctxt,nms)
#else
                                 TyConI (DataD ctxt _ nms _ _) -> (ctxt,nms)
                                 TyConI (NewtypeD ctxt _ nms _ _) -> (ctxt,nms)
#endif

                                 TyConI (TySynD _ nms _) -> ([],nms)
                                 _ -> error "IxSet.inferIxSet typeInfo unexpected match"

             names = map tyVarBndrToName binders

             typeCon = List.foldl' appT (conT typeName) (map varT names)
#if MIN_VERSION_template_haskell(2,10,0)
             mkCtx c = List.foldl' appT (conT c)
#else
             mkCtx = classP
#endif
             dataCtxConQ = concat [[mkCtx ''Data [varT name], mkCtx ''Ord [varT name]] | name <- names]
             fullContext = do
                dataCtxCon <- sequence dataCtxConQ
                return (context ++ dataCtxCon)
         case calInfo of
#if MIN_VERSION_template_haskell(2,11,0)
           VarI _ _t _ ->
#else
           VarI _ _t _ _ ->
#endif
               let {-
                   calType = getCalType t
                   getCalType (ForallT _names _ t') = getCalType t'
                   getCalType (AppT (AppT ArrowT _) t') = t'
                   getCalType t' = error ("Unexpected type in getCalType: " ++ pprint t')
                   -}
                   mkEntryPoint n = (conE 'Ix) `appE`
                                    (sigE (varE 'Map.empty) (forallT
#if MIN_VERSION_template_haskell(2,17,0)
                                                             (map (SpecifiedSpec <$) binders)
#else
                                                             binders
#endif
                                                             (return context) $
                                                             appT (appT (conT ''Map) (conT n))
                                                                      (appT (conT ''Set) typeCon))) `appE`
                                    (varE 'flattenWithCalcs `appE` varE calName)
                   mkTypeList :: [TypeQ] -> TypeQ
                   mkTypeList = foldr (\ x xs -> promotedConsT `appT` x `appT` xs) promotedNilT
                   typeList :: TypeQ
                   typeList = mkTypeList (map conT entryPoints)
               in do i <- instanceD (fullContext)
                          (conT ''Indexable `appT` typeList `appT` typeCon)
                          [valD (varP 'indices) (normalB (appsE ([| ixList |] : map mkEntryPoint entryPoints))) []]
                     let ixType = conT ''IxSet `appT` typeList `appT` typeCon
                     ixType' <- tySynD (mkName ixset) binders ixType
                     return $ [i, ixType']  -- ++ d
           _ -> error "IxSet.inferIxSet calInfo unexpected match"

#if MIN_VERSION_template_haskell(2,17,0)
tyVarBndrToName :: TyVarBndr flag -> Name
tyVarBndrToName (PlainTV nm _) = nm
tyVarBndrToName (KindedTV nm _ _) = nm
#else
tyVarBndrToName :: TyVarBndr -> Name
tyVarBndrToName (PlainTV nm) = nm
tyVarBndrToName (KindedTV nm _) = nm
#endif

-- | Generically traverses the argument to find all occurences of
-- values of type @b@ and returns them as a list.
--
-- This function properly handles 'String' as 'String' not as @['Char']@.
flatten :: (Typeable a, Data a, Typeable b) => a -> [b]
flatten x = case cast x of
              Just y -> case cast (y :: String) of
                          Just v -> [v]
                          Nothing -> []
              Nothing -> case cast x of
                           Just v -> v : concat (gmapQ flatten x)
                           Nothing -> concat (gmapQ flatten x)

-- | Generically traverses the argument and calculated values to find
-- all occurences of values of type @b@ and returns them as a
-- list. Equivalent to:
--
-- > flatten (x,calcs x)
--
-- This function properly handles 'String' as 'String' not as @['Char']@.
flattenWithCalcs :: (Data c,Typeable a, Data a, Typeable b) => (a -> c) -> a -> [b]
flattenWithCalcs calcs x = flatten (x,calcs x)

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
change :: forall ixs a. Indexable ixs a
       => SetOp -> IndexOp -> a -> IxSet ixs a -> IxSet ixs a
change opS opI x (IxSet a indexes) = IxSet (opS x a) v
  where
    v :: IxList ixs a
    v = mapIxList' update indexes

    update :: forall ix. Ord ix => Ix ix a -> Ix ix a
    update (Ix index f) = Ix index' f
      where
        ds :: [ix]
        ds = f x
        ii :: forall k. Ord k => Map k (Set a) -> k -> Map k (Set a)
        ii m dkey = opI dkey x m
        index' :: Map ix (Set a)
        index' = List.foldl' ii index ds

insertList :: forall ixs a. Indexable ixs a
           => [a] -> IxSet ixs a -> IxSet ixs a
insertList xs (IxSet a indexes) = IxSet (List.foldl' (\ b x -> Set.insert x b) a xs) v
  where
    v :: IxList ixs a
    v = mapIxList' update indexes

    update :: forall ix. Ord ix => Ix ix a -> Ix ix a
    update (Ix index f) = Ix index' f
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- xs, k <- f x]

        index' :: Map ix (Set a)
        index' = Ix.insertList dss index

-- | Internal helper function that takes a partial index from one index
-- set and rebuilds the rest of the structure of the index set.
--
-- Slightly rewritten comment from original version regarding dss / index':
--
-- We try to be really clever here. The partialindex is a Map of Sets
-- from original index. We want to reuse it as much as possible. If there
-- was a guarantee that each element is present at at most one key we
-- could reuse originalindex as it is. But there can be more, so we need to
-- add remaining ones (in updateh). Anyway we try to reuse old structure and
-- keep new allocations low as much as possible.
fromMapOfSets :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
              => Map ix (Set a) -> IxSet ixs a
fromMapOfSets partialindex =
    IxSet a (mapAt updateh updatet indices)
  where
    a :: Set a
    a = Set.unions (Map.elems partialindex)

    xs :: [a]
    xs = Set.toList a

    -- Update function for the index corresponding to partialindex.
    updateh :: Ix ix a -> Ix ix a
    updateh (Ix _ f) = Ix ix f
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- xs, k <- f x, not (Map.member k partialindex)]

        ix :: Map ix (Set a)
        ix = Ix.insertList dss partialindex

    -- Update function for all other indices.
    updatet :: forall ix'. Ord ix' => Ix ix' a -> Ix ix' a
    updatet (Ix _ f) = Ix ix f
      where
        dss :: [(ix', a)]
        dss = [(k, x) | x <- xs, k <- f x]

        ix :: Map ix' (Set a)
        ix = Ix.fromList dss

-- | Inserts an item into the 'IxSet'. If your data happens to have
-- a primary key this function might not be what you want. See
-- 'updateIx'.
insert :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
insert = change Set.insert Ix.insert

-- | Removes an item from the 'IxSet'.
delete :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
delete = change Set.delete Ix.delete

-- | Remove every item in the second 'IxSet' from the first 'IxSet'.
difference :: forall ixs a. Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
difference (IxSet elements ixs) (IxSet deletes deleteIxs) =
  IxSet (elements `Set.difference` deletes) $
    zipWithIxList' diffIx ixs deleteIxs
  where
  diffIx (Ix ix ixer) (Ix delIx _) = Ix (Ix.difference ix delIx) ixer

-- | Remove every element of a 'Set' from an 'IxSet'.
deleteSet :: Indexable ixs a => Set a -> IxSet ixs a -> IxSet ixs a
deleteSet deletes set = set `difference` fromSet deletes

-- | Remove elements from an `IxSet` not matching a predicate.
filter :: Indexable ixs a => (a -> Bool) -> IxSet ixs a -> IxSet ixs a
filter p ixset@(IxSet elements _ixs) =
  ixset `difference` fromSet (Set.filter (not . p) elements)

-- | Will replace the item with the given index of type 'ix'.
-- Only works if there is at most one item with that index in the 'IxSet'.
-- Will not change 'IxSet' if you have more than one item with given index.
updateIx :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> a -> IxSet ixs a -> IxSet ixs a
updateIx i new ixset = insert new $
                     maybe ixset (flip delete ixset) $
                     getOne $ ixset @= i

-- | Will delete the item with the given index of type 'ix'.
-- Only works if there is at  most one item with that index in the 'IxSet'.
-- Will not change 'IxSet' if you have more than one item with given index.
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
fromSet :: (Indexable ixs a) => Set a -> IxSet ixs a
fromSet = fromList . Set.toList

-- | Converts a list to an 'IxSet'.
fromList :: (Indexable ixs a) => [a] -> IxSet ixs a
fromList list = insertList list empty

-- | Returns the number of unique items in the 'IxSet'.
size :: IxSet ixs a -> Int
size = Set.size . toSet

-- | Converts an 'IxSet' to its list of elements.
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
getOne :: Ord a => IxSet ixs a -> Maybe a
getOne ixset = case toList ixset of
                   [x] -> Just x
                   _   -> Nothing

-- | Like 'getOne' with a user-provided default.
getOneOr :: Ord a => a -> IxSet ixs a -> a
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

(\\\) :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
(\\\) = difference

infixr 5 &&&
infixr 5 |||

-- | Takes the union of the two 'IxSet's.
union :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
union (IxSet a1 x1) (IxSet a2 x2) =
  IxSet (Set.union a1 a2)
    (zipWithIxList' (\ (Ix a f) (Ix b _) -> Ix (Ix.union a b) f) x1 x2)
-- TODO: function is taken from the first

-- | Takes the intersection of the two 'IxSet's.
intersection :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
intersection (IxSet a1 x1) (IxSet a2 x2) =
  IxSet (Set.intersection a1 a2)
    (zipWithIxList' (\ (Ix a f) (Ix b _) -> Ix (Ix.intersection a b) f) x1 x2)
-- TODO: function is taken from the first

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

-- | Returns the subset with an index equal to the provided key.  The
-- set must be indexed over key type, doing otherwise results in
-- runtime error.
getEQ :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getEQ = getOrd EQ

-- | Returns the subset with an index less than the provided key.  The
-- set must be indexed over key type, doing otherwise results in
-- runtime error.
getLT :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getLT = getOrd LT

-- | Returns the subset with an index greater than the provided key.
-- The set must be indexed over key type, doing otherwise results in
-- runtime error.
getGT :: (Indexable ixs a, IsIndexOf ix ixs)
      => ix -> IxSet ixs a -> IxSet ixs a
getGT = getOrd GT

-- | Returns the subset with an index less than or equal to the
-- provided key.  The set must be indexed over key type, doing
-- otherwise results in runtime error.
getLTE :: (Indexable ixs a, IsIndexOf ix ixs)
       => ix -> IxSet ixs a -> IxSet ixs a
getLTE = getOrd2 True True False

-- | Returns the subset with an index greater than or equal to the
-- provided key.  The set must be indexed over key type, doing
-- otherwise results in runtime error.
getGTE :: (Indexable ixs a, IsIndexOf ix ixs)
       => ix -> IxSet ixs a -> IxSet ixs a
getGTE = getOrd2 False True True

-- | Returns the subset with an index within the interval provided.
-- The bottom of the interval is closed and the top is open,
-- i. e. [k1;k2).  The set must be indexed over key type, doing
-- otherwise results in runtime error.
getRange :: (Indexable ixs a, IsIndexOf ix ixs)
         => ix -> ix -> IxSet ixs a -> IxSet ixs a
getRange k1 k2 ixset = getGTE k1 (getLT k2 ixset)

-- | Returns lists of elements paired with the indices determined by
-- type inference.
groupBy :: forall ix ixs a. IsIndexOf ix ixs => IxSet ixs a -> [(ix, [a])]
groupBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index _) = map (second Set.toList) (Map.toList index)

-- | Returns the list of index keys being used for a particular index.
indexKeys :: forall ix ixs a . IsIndexOf ix ixs => IxSet ixs a -> [ix]
indexKeys (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [ix]
    f (Ix index _) = Map.keys index

-- | Returns lists of elements paired with the indices determined by
-- type inference.
--
-- The resulting list will be sorted in ascending order by 'ix'.
-- The values in @[a]@ will be sorted in ascending order as well.
groupAscBy :: forall ix ixs a. IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupAscBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index _) = map (second Set.toAscList) (Map.toAscList index)

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
groupDescBy (IxSet _ indexes) = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index _) = map (second Set.toAscList) (Map.toDescList index)

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.  The set must be indexed over key type,
-- doing otherwise results in runtime error.

getOrd :: (Indexable ixs a, IsIndexOf ix ixs)
       => Ordering -> ix -> IxSet ixs a -> IxSet ixs a
getOrd LT = getOrd2 True False False
getOrd EQ = getOrd2 False True False
getOrd GT = getOrd2 False False True

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.  The set must be indexed over key type,
-- doing otherwise results in runtime error.
getOrd2 :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
        => Bool -> Bool -> Bool -> ix -> IxSet ixs a -> IxSet ixs a
getOrd2 inclt inceq incgt v (IxSet _ ixs) = f (access ixs)
  where
    f :: Ix ix a -> IxSet ixs a
    f (Ix index _) = fromMapOfSets result
      where
        lt', gt' :: Map ix (Set a)
        eq' :: Maybe (Set a)
        (lt', eq', gt') = Map.splitLookup v index

        lt, gt :: Map ix (Set a)
        lt = if inclt then lt' else Map.empty
        gt = if incgt then gt' else Map.empty
        eq :: Maybe (Set a)
        eq = if inceq then eq' else Nothing

        ltgt :: Map ix (Set a)
        ltgt = Map.unionWith Set.union lt gt

        result :: Map ix (Set a)
        result = case eq of
          Just eqset -> Map.insertWith Set.union v eqset ltgt
          Nothing    -> ltgt

-- Optimization todo:
--
--   * can we avoid rebuilding the collection every time we query?
--     does laziness take care of everything?
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
stats :: Indexable ixs a => IxSet ixs a -> (Int,Int,Int,Int)
stats (IxSet a ixs) = (no_elements,no_indexes,no_keys,no_values)
    where
      no_elements = Set.size a
      no_indexes  = lengthIxList ixs
      no_keys     = sum (ixListToList (\ (Ix m _) -> Map.size m) ixs)
      no_values   = sum (ixListToList (\ (Ix m _) -> sum [Set.size s | s <- Map.elems m]) ixs)

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{- |
An efficient implementation of queryable sets.

Assume you have a family of types such as:

> data Entry      = Entry Author [Author] Updated Id Content
>   deriving (Show, Eq, Ord, Data)
> newtype Updated = Updated UTCTime
>   deriving (Show, Eq, Ord, Data)
> newtype Id      = Id Int64
>   deriving (Show, Eq, Ord, Data)
> newtype Content = Content String
>   deriving (Show, Eq, Ord, Data)
> newtype Author  = Author Email
>   deriving (Show, Eq, Ord, Data)
> type Email      = String
> data Test = Test
>   deriving (Show, Eq, Ord, Data)

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

    The use of 'ixGen' requires the 'Data' instances above.
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

= Strictness

An 'IxSet' is "mostly" spine-strict: it is generally spine-strict
in the set itself, but tries to avoid building the indices until they are
needed. Thus:

 * Construction operations ('fromSet' and 'fromList') will evaluate the elements
   to build the underlying set, but will build the indices lazily. Since the
   only data the index construction retains are elements of the set, this should not
   cause a significant space leak.  However, if you wish to perform the index
   construction up front rather than deferring it until the indices are forced,
   use 'forceIndices'.

 * Index lookups (such as 'getEQ') and other query operations (including 'filter',
   'union' and 'intersection') are lazy in the indices, so querying a number of
   times and subsequently selecting the result will not unnecessarily rebuild all
   indices. This could result in a space leak if you repeatedly query and then
   retain the resulting 'IxSet' without looking at the results.  Again, you can
   use 'forceIndices' to avoid this.

 * Operations that modify 'IxSet' (e.g. 'insert', 'delete', 'updateIx') are
   spine-strict in the indices as well. This avoids retaining old copies of the
   'IxSet' as it is modified.  There are currently no lazy modification operations.

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
     insertSet,
     insertMany,
     delete,
     deleteSet,
     deleteMany,
     updateIx,
     deleteIx,
     deleteIxMany,

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
     filter,

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

     -- * Lookup
     lookupIx,
     lookupIxMany,

     -- * Grouping
     groupBy,
     groupAscBy,
     groupDescBy,
     indexKeys,

     -- * Index creation helpers
     flatten,
     flattenWithCalcs,

     -- * Debugging and optimization
     forceIndices,
     stats
)
where

import           Data.Generics  (Data, gmapQ)
import           Data.IxSet.Typed.Internal.Ix  (Ix(Ix))
import           Data.IxSet.Typed.Internal.IxList
import           Data.IxSet.Typed.Internal.IxSet
import qualified Data.List      as List
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Set       (Set)
import           Data.Typeable  (Typeable, cast)
import           Language.Haskell.TH as TH hiding (Type)
import           Prelude hiding (filter, null)

--------------------------------------------------------------------------
-- 'IxSet' construction
--------------------------------------------------------------------------

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
ixFun :: (a -> [ix]) -> Ix ix a
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
ixGen :: forall proxy a ix. (Data a, Typeable ix) => proxy ix -> Ix ix a
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
-- >   deriving (Eq, Ord, Data)
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
                                 TyConI (DataD ctxt _ nms _ _ _) -> (ctxt,nms)
                                 TyConI (NewtypeD ctxt _ nms _ _ _) -> (ctxt,nms)
                                 TyConI (TySynD _ nms _) -> ([],nms)
                                 _ -> error "IxSet.inferIxSet typeInfo unexpected match"

             names = map tyVarBndrToName binders

             typeCon = List.foldl' appT (conT typeName) (map varT names)

             mkCtx c = List.foldl' appT (conT c)

             dataCtxConQ = concat [[mkCtx ''Data [varT name], mkCtx ''Ord [varT name]] | name <- names]
             fullContext = do
                dataCtxCon <- sequence dataCtxConQ
                return (context ++ dataCtxCon)
         case calInfo of
           VarI _ _t _ ->
               let {-
                   calType = getCalType t
                   getCalType (ForallT _names _ t') = getCalType t'
                   getCalType (AppT (AppT ArrowT _) t') = t'
                   getCalType t' = error ("Unexpected type in getCalType: " ++ pprint t')
                   -}
                   mkEntryPoint n = (conE 'Ix) `appE`
                                    (sigE (varE 'Map.empty) (forallT
                                                             (map (SpecifiedSpec <$) binders)
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

tyVarBndrToName :: TyVarBndr flag -> Name
tyVarBndrToName (PlainTV nm _) = nm
tyVarBndrToName (KindedTV nm _ _) = nm

-- | Generically traverses the argument to find all occurences of
-- values of type @b@ and returns them as a list.
--
-- This function properly handles 'String' as 'String' not as @['Char']@.
flatten :: (Data a, Typeable b) => a -> [b]
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
flattenWithCalcs :: (Data c, Data a, Typeable b) => (a -> c) -> a -> [b]
flattenWithCalcs calcs x = flatten (x,calcs x)

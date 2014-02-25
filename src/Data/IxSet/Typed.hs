{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleInstances,
             MultiParamTypeClasses, TemplateHaskell, RankNTypes,
             FunctionalDependencies, DeriveDataTypeable,
             GADTs, CPP, ScopedTypeVariables, KindSignatures,
             DataKinds, TypeOperators, StandaloneDeriving,
             TypeFamilies, ScopedTypeVariables, ConstraintKinds,
             FunctionalDependencies #-}

{- |
An efficient implementation of queryable sets.

Assume you have a type like:

> data Entry = Entry Author [Author] Updated Id Content
> newtype Updated = Updated EpochTime
> newtype Id = Id Int64
> newtype Content = Content String
> newtype Author = Author Email
> type Email = String

1. Decide what parts of your type you want indexed and make your type
an instance of 'Indexable'. Use 'ixFun' and 'ixGen' to build indexes:

> instance Indexable Entry where
>     empty = ixSet
>               [ ixGen (Proxy :: Proxy Author)        -- out of order
>               , ixGen (Proxy :: Proxy Id)
>               , ixGen (Proxy :: Proxy Updated)
>               , ixGen (Proxy :: Proxy Test)          -- bogus index
>               ]

3. Use 'insert', 'delete', 'updateIx', 'deleteIx' and 'empty' to build
   up an 'IxSet' collection:

> entries = foldr insert empty [e1,e2,e3,e4]
> entries' = foldr delete entries [e1,e3]
> entries'' = update e4 e5 entries

4. Use the query functions below to grab data from it:

> entries @= (Author "john@doe.com") @< (Updated t1)

Statement above will find all items in entries updated earlier than
@t1@ by @john\@doe.com@.

5. Text index

If you want to do add a text index create a calculated index.  Then if you want
all entries with either @word1@ or @word2@, you change the instance
to:

> getWords (Entry _ _ _ _ (Content s)) = map Word $ words s
>
> instance Indexable Entry where
>     empty = ixSet [ ...
>                     ixFun getWords
>                   ]

Now you can do this query to find entries with any of the words:

> entries @+ [Word "word1", Word "word2"]

And if you want all entries with both:

> entries @* [Word "word1", Word "word2"]

6. Find only the first author

If an @Entry@ has multiple authors and you want to be able to query on
the first author only, define a @FirstAuthor@ datatype and create an
index with this type.  Now you can do:

> newtype FirstAuthor = FirstAuthor Email
>
> getFirstAuthor (Entry author _ _ _ _) = [FirstAuthor author]
>
> instance Indexable Entry where
>     ...
>     empty = ixSet [ ...
>                     ixFun getFirstAuthor
>                   ]
>
>     entries @= (FirstAuthor "john@doe.com")  -- guess what this does

-}

module Data.IxSet.Typed
    (
     -- * Set type
     IxSet,
     Indexable(..),
     Proxy(..),
     noCalcs,
     inferIxSet,
     ixSet,
     ixFun,
     ixGen,

     -- * Changes to set
     IndexOp,
     change,
     insert,
     delete,
     updateIx,
     deleteIx,

     -- * Creation
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
     union,
     intersection,

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

     -- * Index creation helpers
     flatten,
     flattenWithCalcs,

     -- * Debugging and optimization
     -- stats
)
where

import Prelude hiding (null)

import           Control.Arrow  (first, second)
import           Data.Generics  (Data, gmapQ)
-- import qualified Data.Generics.SYB.WithClass.Basics as SYBWC
import qualified Data.IxSet.Typed.Ix  as Ix
import           Data.IxSet.Typed.Ix  (Ix(Ix))
import qualified Data.List      as List
import           Data.Map       (Map)
import qualified Data.Map       as Map
import           Data.Maybe     (fromMaybe)
import           Data.Monoid    (Monoid(mempty, mappend))
import           Data.SafeCopy  (SafeCopy(..), contain, safeGet, safePut)
import           Data.Set       (Set)
import qualified Data.Set       as Set
import           Data.Typeable  (Typeable, cast, typeOf)
import Language.Haskell.TH      as TH
import GHC.Exts (Constraint)


-------------------------------------------------
-- Type proxies

data Proxy a = Proxy

-- the core datatypes

-- | Set with associated indexes.
data IxSet (ixs :: [*]) (a :: *) where
  Nil   :: IxSet '[] a
  (:::) :: Ix ix a -> IxSet ixs a -> IxSet (ix ': ixs) a

-- deriving instance Data (IxSet ixs a)
-- deriving instance Typeable IxSet

infixr 5 :::

mapIxSet :: (All Ord ixs)
         => (forall ix. Ord ix => Ix ix a -> Ix ix a)
         -> IxSet ixs a -> IxSet ixs a
mapIxSet _ Nil        = Nil
mapIxSet f (x ::: xs) = f x ::: mapIxSet f xs

zipWithIxSet :: (All Ord ixs)
             => (forall ix. Ord ix => Ix ix a -> Ix ix a -> Ix ix a)
             -> IxSet ixs a -> IxSet ixs a -> IxSet ixs a
zipWithIxSet _ Nil        Nil        = Nil
zipWithIxSet f (x ::: xs) (y ::: ys) = f x y ::: zipWithIxSet f xs ys
zipWithIxSet _ _          _          = error "Data.IxSet.Typed.zipWithIxSet: impossible"

class Ord ix => IsIndexOf (ix :: *) (ixs :: [*]) where
  access :: IxSet ixs a -> Ix ix a
  mapAt :: (All Ord ixs)
        => (Ix ix a -> Ix ix a)
        -> (forall ix. Ord ix => Ix ix a -> Ix ix a)
        -> IxSet ixs a -> IxSet ixs a

instance Ord ix => IsIndexOf ix (ix ': ixs) where
  access (x ::: _xs)     = x
  mapAt fh ft (x ::: xs) = fh x ::: mapIxSet ft xs

instance IsIndexOf ix ixs => IsIndexOf ix (ix' ': ixs) where
  access (_x ::: xs)     = access xs
  mapAt fh ft (x ::: xs) = ft x ::: mapAt fh ft xs

-- | Create an 'IxSet' using a list of indexes. Useful in the 'Indexable'
-- 'empty' method. Use 'ixFun' and 'ixGen' as list elements.
--
-- > instance Indexable Type where
-- >     empty = ixSet [ ...
-- >                     ixFun getIndex1
-- >                     ixGen (Proxy :: Proxy Index2Type)
-- >                   ]
--
-- Every value in the 'IxSet' must be reachable by the first index in this
-- list, or you'll get a runtime error.
ixSet :: MkIxSet ixs ixs a r => r
ixSet = ixSet' id

class MkIxSet ixs ixs' a r | r -> a ixs ixs' where
  ixSet' :: (IxSet ixs a -> IxSet ixs' a) -> r

instance MkIxSet '[] ixs a (IxSet ixs a) where
  ixSet' acc = acc Nil

instance MkIxSet ixs ixs' a r => MkIxSet (ix ': ixs) ixs' a (Ix ix a -> r) where
  ixSet' acc ix = ixSet' (\ x -> acc (ix ::: x))

-- | Create a functional index. Provided function should return a list
-- of indexes where the value should be found.
--
-- > getIndexes value = [...indexes...]
--
-- > instance Indexable Type where
-- >     empty = ixSet [ ixFun getIndexes ]
--
-- This is the recommended way to create indexes.
ixFun :: Ord ix => (a -> [ix]) -> Ix ix a
ixFun = Ix Map.empty


-- | Create a generic index. Provided example is used only as type source
-- so you may use a 'Proxy'. This uses flatten to traverse values using
-- their 'Data' instances.
--
-- > instance Indexable Type where
-- >     empty = ixSet [ ixGen (Proxy :: Proxy Type) ]
--
-- In production systems consider using 'ixFun' in place of 'ixGen' as
-- the former one is much faster.
ixGen :: forall a ix. (Ord ix, Data a, Typeable ix) => Proxy ix -> Ix ix a
ixGen _proxy = ixFun (flatten :: a -> [ix])

{-
showTypeOf :: (Typeable a) => a -> String
showTypeOf x = showsPrec 11 (typeOf x) []
-}

instance Indexable ixs a => Eq (IxSet ixs a) where
  Ix a _ ::: _ == Ix b _ ::: _ = a == b
  Nil          == Nil          = True
  _            == _            = error "Data.IxSet.Typed.(==): impossible"
-- TODO: original ixset disallows an IxSet without an index;
-- should we do the same?

instance Indexable ixs a => Ord (IxSet ixs a) where
  compare a b = compare (toSet a) (toSet b)

{- FIXME
instance Version (IxSet a)
instance (Serialize a, Ord a, Typeable a, Indexable a) => Serialize (IxSet a) where
    putCopy = contain . safePut . toList
    getCopy = contain $ liftM fromList safeGet
-}

instance (Indexable ixs a, SafeCopy a) => SafeCopy (IxSet ixs a) where
  putCopy = contain . safePut . toList
  getCopy = contain $ fmap fromList safeGet

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

{- FIXME
instance (Indexable a, Ord a,Data a, Default a) => Default (IxSet a) where
    defaultValue = empty
-}
instance (Indexable ixs a, Show a) => Show (IxSet ixs a) where
    showsPrec prec = showsPrec prec . toSet

instance (Indexable ixs a, Read a) => Read (IxSet ixs a) where
    readsPrec n = map (first fromSet) . readsPrec n

type family All (c :: * -> Constraint) (xs :: [*]) :: Constraint
type instance All c '[]       = ()
type instance All c (x ': xs) = (c x, All c xs)

-- | Defines objects that can be members of 'IxSet'.
class (All Ord ixs, Ord a) => Indexable ixs a where
  -- | Defines what an empty 'IxSet' for this particular type should look
  -- like.  It should have all necessary indexes. Use the 'ixSet'
  -- function to create the set and fill it in with 'ixFun' and 'ixGen'.
  empty :: IxSet ixs a

-- | Function to be used for 'calcs' in 'inferIxSet' when you don't
-- want any calculated values.
noCalcs :: t -> ()
noCalcs _ = ()

{- | Template Haskell helper function for automatically building an
'Indexable' instance from a data type, e.g.

> data Foo = Foo Int String

and

> $(inferIxSet "FooDB" ''Foo 'noCalcs [''Int,''String])

will build a type synonym

> type FooDB = IxSet Foo

with @Int@ and @String@ as indexes.

/WARNING/: The type specified as the first index must be a type which
appears in all values in the 'IxSet' or 'toList', 'toSet' and
serialization will not function properly.  You will be warned not to do
this with a runtime error.  You can always use the element type
itself. For example:

> $(inferIxSet "FooDB" ''Foo 'noCalcs [''Foo, ''Int, ''String])

-}
inferIxSet :: String -> TH.Name -> TH.Name -> [TH.Name] -> Q [Dec]
inferIxSet _ _ _ [] = error "inferIxSet needs at least one index"
inferIxSet ixset typeName calName entryPoints
    = do calInfo <- reify calName
         typeInfo <- reify typeName
         let (context,binders) = case typeInfo of
                                 TyConI (DataD ctxt _ nms _ _) -> (ctxt,nms)
                                 TyConI (NewtypeD ctxt _ nms _ _) -> (ctxt,nms)
                                 TyConI (TySynD _ nms _) -> ([],nms)
                                 _ -> error "IxSet.inferIxSet typeInfo unexpected match"

             names = map tyVarBndrToName binders

             typeCon = List.foldl' appT (conT typeName) (map varT names)
             mkCtx = classP
             dataCtxConQ = concat [[mkCtx ''Data [varT name], mkCtx ''Ord [varT name]] | name <- names]
             fullContext = do
                dataCtxCon <- sequence dataCtxConQ
                return (context ++ dataCtxCon)
         case calInfo of
           VarI _ _t _ _ ->
               let {-
                   calType = getCalType t
                   getCalType (ForallT _names _ t') = getCalType t'
                   getCalType (AppT (AppT ArrowT _) t') = t'
                   getCalType t' = error ("Unexpected type in getCalType: " ++ pprint t')
                   -}
                   mkEntryPoint n = (conE 'Ix) `appE`
                                    (sigE (varE 'Map.empty) (forallT binders (return context) $
                                                             appT (appT (conT ''Map) (conT n))
                                                                      (appT (conT ''Set) typeCon))) `appE`
                                    (varE 'flattenWithCalcs `appE` varE calName)
                   mkTypeList :: [TypeQ] -> TypeQ
                   mkTypeList = foldr (\ x xs -> promotedConsT `appT` x `appT` xs) promotedNilT
                   typeList :: TypeQ
                   typeList = mkTypeList (map conT entryPoints)
               in do i <- instanceD (fullContext)
                          (conT ''Indexable `appT` typeList `appT` typeCon)
                          [valD (varP 'empty) (normalB (appsE ([| ixSet |] : map mkEntryPoint entryPoints))) []]
                     let ixType = conT ''IxSet `appT` typeList `appT` typeCon
                     ixType' <- tySynD (mkName ixset) binders ixType
                     return $ [i, ixType']  -- ++ d
           _ -> error "IxSet.inferIxSet calInfo unexpected match"

tyVarBndrToName :: TyVarBndr -> Name
tyVarBndrToName (PlainTV nm) = nm
tyVarBndrToName (KindedTV nm _) = nm

-- modification operations

type IndexOp =
    forall k a. (Ord k,Ord a) => k -> a -> Map k (Set a) -> Map k (Set a)

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

-- | Higher order operator for modifying 'IxSet's.  Use this when your
-- final function should have the form @a -> 'IxSet' a -> 'IxSet' a@,
-- e.g. 'insert' or 'delete'.
change :: forall ixs a. (Indexable ixs a) =>
          IndexOp -> a -> IxSet ixs a -> IxSet ixs a
change op x indexes = v
  where
    v :: IxSet ixs a
    v = mapIxSet update indexes

    update :: forall ix. Ord ix => Ix ix a -> Ix ix a
    update (Ix index f) = Ix index' f
      where
        ds :: [ix]
        ds = f x
        ii :: forall k. Ord k => Map k (Set a) -> k -> Map k (Set a)
        ii m dkey = op dkey x m
        index' :: Map ix (Set a)
        index' = List.foldl' ii index ds
-- TODO: the "first index check" isn't implemented

insertList :: forall ixs a. (Indexable ixs a)
            => [a] -> IxSet ixs a -> IxSet ixs a
insertList xs indexes = v
  where
    v :: IxSet ixs a
    v = mapIxSet update indexes

    update :: forall ix. Ord ix => Ix ix a -> Ix ix a
    update (Ix index f) = Ix index' f
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- xs, k <- f x]

        index' :: Map ix (Set a)
        index' = Ix.insertList dss index
-- TODO: the "first index check isn't implemented

insertMapOfSets :: forall ixs ix a. (Indexable ixs a, IsIndexOf ix ixs)
                => Map ix (Set a) -> IxSet ixs a -> IxSet ixs a
insertMapOfSets originalindex indexes = mapAt updateh updatet indexes
  where
    xs :: [a]
    xs = concatMap Set.toList (Map.elems originalindex)

    updateh :: Ix ix a -> Ix ix a
    updateh (Ix _index f) = Ix index' f
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- xs, k <- f x]

        dssf :: [(ix, a)]
        dssf = filter (\ (k, _) -> not (Map.member k originalindex)) dss

        index' :: Map ix (Set a)
        index' = Ix.insertList dssf originalindex

    updatet :: forall ix. Ord ix => Ix ix a -> Ix ix a
    updatet (Ix index f) = Ix index' f
      where
        dss :: [(ix, a)]
        dss = [(k, x) | x <- xs, k <- f x]

        index' :: Map ix (Set a)
        index' = Ix.insertList dss index
-- TODO: Comment from original version regarding dss / index':
--
-- We try to be really clever here. The originalindex is a Map of Sets
-- from original index. We want to reuse it as much as possible. If there
-- was a guarantee that each element is present at at most one index we
-- could reuse originalindex as it is. But there can be more, so we need to
-- add remaining ones. Anyway we try to reuse old structure and keep
-- new allocations low as much as possible.

-- | Inserts an item into the 'IxSet'. If your data happens to have
-- a primary key this function might not be what you want. See
-- 'updateIx'.
insert :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
insert = change Ix.insert

-- | Removes an item from the 'IxSet'.
delete :: Indexable ixs a => a -> IxSet ixs a -> IxSet ixs a
delete = change Ix.delete

-- | Will replace the item with index k.  Only works if there is at
-- most one item with that index in the 'IxSet'. Will not change
-- 'IxSet' if you have more then 1 item with given index.
updateIx :: (Indexable ixs a, IsIndexOf ix ixs, Ord ix)
         => ix -> a -> IxSet ixs a -> IxSet ixs a
updateIx i new ixset = insert new $
                     maybe ixset (flip delete ixset) $
                     getOne $ ixset @= i

-- | Will delete the item with index k.  Only works if there is at
-- most one item with that index in the 'IxSet'. Will not change
-- 'IxSet' if you have more then 1 item with given index.
deleteIx :: (Indexable ixs a, IsIndexOf ix ixs, Ord ix)
         => ix -> IxSet ixs a -> IxSet ixs a
deleteIx i ixset = maybe ixset (flip delete ixset) $
                       getOne $ ixset @= i

-- conversion operations

-- | Converts an 'IxSet' to a 'Set' of its elements.
toSet :: Ord a => IxSet ixs a -> Set a
toSet (Ix ix _ ::: _) = Set.unions (Map.elems ix)
toSet Nil             = Set.empty

-- | Converts a 'Set' to an 'IxSet'.
fromSet :: (Indexable ixs a) => Set a -> IxSet ixs a
fromSet = fromList . Set.toList

-- | Converts a list to an 'IxSet'.
fromList :: (Indexable ixs a) => [a] -> IxSet ixs a
fromList list = insertList list empty

-- | Returns the number of unique items in the 'IxSet'.
size :: Ord a => IxSet ixs a -> Int
size = Set.size . toSet

-- | Converts an 'IxSet' to its list of elements.
toList :: Ord a => IxSet ixs a -> [a]
toList = Set.toList . toSet

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in ascending order by the index 'ix'.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toAscList :: forall ix ixs a. IsIndexOf ix ixs => Proxy ix -> IxSet ixs a -> [a]
toAscList _ ixset = concatMap snd (groupAscBy ixset :: [(ix, [a])])

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in descending order by the index 'ix'.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toDescList :: forall ix ixs a. IsIndexOf ix ixs => Proxy ix -> IxSet ixs a -> [a]
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
null (Ix ix _ ::: _) = Map.null ix
null Nil             = True

-- set operations

-- | An infix 'intersection' operation.
(&&&) :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
(&&&) = intersection

-- | An infix 'union' operation.
(|||) :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
(|||) = union

infixr 5 &&&
infixr 5 |||

-- | Takes the union of the two 'IxSet's.
union :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
union x1 x2 = zipWithIxSet (\ (Ix a f) (Ix b _) -> Ix (Ix.union a b) f) x1 x2
-- TODO: function is taken from the first

-- | Takes the intersection of the two 'IxSet's.
intersection :: Indexable ixs a => IxSet ixs a -> IxSet ixs a -> IxSet ixs a
intersection x1 x2 = zipWithIxSet (\ (Ix a f) (Ix b _) -> Ix (Ix.intersection a b) f) x1 x2
-- TODO: function is taken from the first

-- query operators

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

-- | Returns the subset with indexes in the open interval (k,k).
(@><) :: (Indexable ixs a, IsIndexOf ix ixs)
      => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @>< (v1,v2) = getLT v2 $ getGT v1 ix

-- | Returns the subset with indexes in [k,k).
(@>=<) :: (Indexable ixs a, IsIndexOf ix ixs)
       => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @>=< (v1,v2) = getLT v2 $ getGTE v1 ix

-- | Returns the subset with indexes in (k,k].
(@><=) :: (Indexable ixs a, IsIndexOf ix ixs)
       => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @><= (v1,v2) = getLTE v2 $ getGT v1 ix

-- | Returns the subset with indexes in [k,k].
(@>=<=) :: (Indexable ixs a, IsIndexOf ix ixs)
        => IxSet ixs a -> (ix, ix) -> IxSet ixs a
ix @>=<= (v1,v2) = getLTE v2 $ getGTE v1 ix

-- | Creates the subset that has an index in the provided list.
(@+) :: (Indexable ixs a, IsIndexOf ix ixs)
     => IxSet ixs a -> [ix] -> IxSet ixs a
ix @+ list = List.foldl' union empty $ map (ix @=) list

-- | Creates the subset that matches all the provided indexes.
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

-- | Returns lists of elements paired with the indexes determined by
-- type inference.
groupBy :: forall ix ixs a. IsIndexOf ix ixs => IxSet ixs a -> [(ix, [a])]
groupBy indexes = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index _) = map (second Set.toList) (Map.toList index)

-- | Returns lists of elements paired with the indexes determined by
-- type inference.
--
-- The resulting list will be sorted in ascending order by 'ix'.
-- The values in '[a]' will be sorted in ascending order as well.
groupAscBy :: forall ix ixs a. IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupAscBy indexes = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index _) = map (second Set.toAscList) (Map.toAscList index)

-- | Returns lists of elements paired with the indexes determined by
-- type inference.
--
-- The resulting list will be sorted in descending order by 'ix'.
--
-- NOTE: The values in '[a]' are currently sorted in ascending
-- order. But this may change if someone bothers to add
-- 'Set.toDescList'. So do not rely on the sort order of '[a]'.
groupDescBy :: IsIndexOf ix ixs =>  IxSet ixs a -> [(ix, [a])]
groupDescBy indexes = f (access indexes)
  where
    f :: Ix ix a -> [(ix, [a])]
    f (Ix index _) = map (second Set.toAscList) (Map.toDescList index)

--query impl function

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
getOrd2 inclt inceq incgt v ixset = f (access ixset)
  where
    f :: Ix ix a -> IxSet ixs a
    f (Ix index _) = insertMapOfSets result empty
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

{--
Optimization todo:

* can we avoid rebuilding the collection every time we query?
  does laziness take care of everything?

* nicer operators?

* nice way to do updates that doesn't involve reinserting the entire data

* can we index on xpath rather than just type?

--}

instance (Indexable ixs a) => Monoid (IxSet ixs a) where
  mempty  = empty
  mappend = union

-- | Statistics about 'IxSet'. This function returns quadruple
-- consisting of 1. total number of elements in the set 2. number of
-- declared indexes 3. number of keys in all indexes 4. number of
-- values in all keys in all indexes. This can aid you in debugging
-- and optimisation.
{-
stats :: (Ord a) => IxSet a -> (Int,Int,Int,Int)
stats (IxSet indexes) = (no_elements,no_indexes,no_keys,no_values)
    where
      no_elements = size (IxSet indexes)
      no_indexes = length indexes
      no_keys = sum [Map.size m | Ix m _ <- indexes]
      no_values = sum [sum [Set.size s | s <- Map.elems m] | Ix m _ <- indexes]
-}

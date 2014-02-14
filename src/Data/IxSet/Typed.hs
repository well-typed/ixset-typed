{-# LANGUAGE UndecidableInstances, OverlappingInstances, FlexibleInstances,
             MultiParamTypeClasses, TemplateHaskell, RankNTypes,
             FunctionalDependencies, DeriveDataTypeable,
             GADTs, CPP, ScopedTypeVariables #-}

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

module Data.IxSet
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
     stats
)
where

import Prelude hiding (null)

import           Control.Arrow  (first, second)
import           Data.Generics  (Data, gmapQ)
import qualified Data.Generics.SYB.WithClass.Basics as SYBWC
import qualified Data.IxSet.Ix  as Ix
import           Data.IxSet.Ix  (Ix(Ix))
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


-------------------------------------------------
-- Type proxies

data Proxy a = Proxy

mkProxy :: a -> Proxy a
mkProxy _ = Proxy

asProxyType :: a -> Proxy a -> a
asProxyType a _ = a

-- the core datatypes

-- | Set with associated indexes.
data IxSet a = IxSet [Ix a]
    deriving (Data, Typeable)

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
ixSet :: [Ix a] -> IxSet a
ixSet = IxSet

-- | Create a functional index. Provided function should return a list
-- of indexes where the value should be found.
--
-- > getIndexes value = [...indexes...]
--
-- > instance Indexable Type where
-- >     empty = ixSet [ ixFun getIndexes ]
--
-- This is the recommended way to create indexes.
ixFun :: forall a b . (Ord b,Typeable b) => (a -> [b]) -> Ix a
ixFun f = Ix Map.empty f


-- | Create a generic index. Provided example is used only as type source
-- so you may use a 'Proxy'. This uses flatten to traverse values using
-- their 'Data' instances.
--
-- > instance Indexable Type where
-- >     empty = ixSet [ ixGen (Proxy :: Proxy Type) ]
--
-- In production systems consider using 'ixFun' in place of 'ixGen' as
-- the former one is much faster.
ixGen :: forall a b . (Data a,Ord b,Typeable b) => Proxy b -> Ix a
ixGen _example = ixFun (flatten :: a -> [b])

showTypeOf :: (Typeable a) => a -> String
showTypeOf x = showsPrec 11 (typeOf x) []

instance (Eq a,Ord a,Typeable a) => Eq (IxSet a) where
    IxSet (Ix a _:_) == IxSet (Ix b _:_) =
        case cast b of
          Just b' -> a==b'
          Nothing -> error "trying to compare two sets with different types of first indexes, this is a bug in the library"
    _ == _ = error "comparing sets without indexes, this is a bug in the library"

instance (Eq a,Ord a,Typeable a) => Ord (IxSet a) where
    compare a b = compare (toSet a) (toSet b)
{- FIXME
instance Version (IxSet a)
instance (Serialize a, Ord a, Typeable a, Indexable a) => Serialize (IxSet a) where
    putCopy = contain . safePut . toList
    getCopy = contain $ liftM fromList safeGet
-}
instance (SafeCopy a, Ord a, Typeable a, Indexable a) => SafeCopy (IxSet a) where
    putCopy = contain . safePut . toList
    getCopy = contain $ fmap fromList safeGet

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


{- FIXME
instance (Indexable a, Ord a,Data a, Default a) => Default (IxSet a) where
    defaultValue = empty
-}
instance (Ord a,Show a) => Show (IxSet a) where
    showsPrec prec = showsPrec prec . toSet

instance (Ord a,Read a,Typeable a,Indexable a) => Read (IxSet a) where
    readsPrec n = map (first fromSet) . readsPrec n

{- | Defines objects that can be members of 'IxSet'.
-}
class Indexable a where
    -- | Defines what an empty 'IxSet' for this particular type should look
    -- like.  It should have all necessary indexes. Use the 'ixSet'
    -- function to create the set and fill it in with 'ixFun' and 'ixGen'.
    empty :: IxSet a

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
#if MIN_VERSION_template_haskell(2,4,0)
             mkCtx = classP
#else
             -- mkType :: Name -> [TypeQ] -> TypeQ
             mkType con = foldl appT (conT con)

             mkCtx = mkType
#endif
             dataCtxConQ = [mkCtx ''Data [varT name] | name <- names]
             fullContext = do
                dataCtxCon <- sequence dataCtxConQ
                return (context ++ dataCtxCon)
         case calInfo of
           VarI _ t _ _ ->
               let calType = getCalType t
                   getCalType (ForallT _names _ t') = getCalType t'
                   getCalType (AppT (AppT ArrowT _) t') = t'
                   getCalType t' = error ("Unexpected type in getCalType: " ++ pprint t')
                   mkEntryPoint n = (conE 'Ix) `appE`
                                    (sigE (varE 'Map.empty) (forallT binders (return context) $
                                                             appT (appT (conT ''Map) (conT n))
                                                                      (appT (conT ''Set) typeCon))) `appE`
                                    (varE 'flattenWithCalcs `appE` varE calName)
               in do i <- instanceD (fullContext)
                          (conT ''Indexable `appT` typeCon)
                          [valD (varP 'empty) (normalB [| ixSet $(listE (map mkEntryPoint entryPoints)) |]) []]
                     let ixType = appT (conT ''IxSet) typeCon
                     ixType' <- tySynD (mkName ixset) binders ixType
                     return $ [i, ixType']  -- ++ d
           _ -> error "IxSet.inferIxSet calInfo unexpected match"

-- | Version of 'instanceD' that takes in a Q [Dec] instead of a [Q Dec]
-- and filters out signatures from the list of declarations.
instanceD' :: CxtQ -> TypeQ -> Q [Dec] -> DecQ
instanceD' ctxt ty decs =
    do decs' <- decs
       let decs'' = filter (not . isSigD) decs'
       instanceD ctxt ty (map return decs'')

-- | Returns true if the Dec matches a SigD constructor.
isSigD :: Dec -> Bool
isSigD (SigD _ _) = True
isSigD _ = False

#if MIN_VERSION_template_haskell(2,4,0)
tyVarBndrToName :: TyVarBndr -> Name
tyVarBndrToName (PlainTV nm) = nm
tyVarBndrToName (KindedTV nm _) = nm
#else
tyVarBndrToName :: a -> a
tyVarBndrToName = id
#endif



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
change :: (Typeable a,Indexable a,Ord a) =>
          IndexOp -> a -> IxSet a -> IxSet a
change op x (IxSet indexes) =
    IxSet v
    where
    v = zipWith update (True:repeat False) indexes
    update firstindex (Ix index flatten2) = Ix index' flatten2
        where
        key = (undefined :: Map key (Set a) -> key) index
        ds = flatten2 x
        ii m dkey = op dkey x m
        index' = if firstindex && List.null ds
                 then error $ "Happstack.Data.IxSet.change: all values must appear in first declared index " ++ showTypeOf key ++ " of " ++ showTypeOf x
                 else List.foldl' ii index ds -- handle multiple values

insertList :: (Typeable a,Indexable a,Ord a)
           => [a] -> IxSet a -> IxSet a
insertList xs (IxSet indexes) =
    IxSet v
    where
    v = zipWith update (True:repeat False) indexes
    update firstindex (Ix index flatten2) = Ix index' flatten2
        where
        key = (undefined :: Map key (Set a) -> key) index
        flattencheck x
            | firstindex = case flatten2 x of
                             [] -> error $ "Happstack.Data.IxSet.change: all values must appear in first declared index " ++ showTypeOf key ++ " of " ++ showTypeOf x
                             res -> res
            | otherwise = flatten2 x
        dss = [(k,x) | x <- xs, k <- flattencheck x]
        index' = Ix.insertList dss index

insertMapOfSets :: (Typeable a, Ord a,Indexable a,Typeable key,Ord key)
                => Map key (Set a) -> IxSet a -> IxSet a
insertMapOfSets originalindex (IxSet indexes) =
    IxSet v
    where
    v = map update indexes
    xs = concatMap Set.toList (Map.elems originalindex)
    update (Ix index flatten2) = Ix index' flatten2
        where
        dss = [(k,x) | x <- xs, k <- flatten2 x]
        {- We try to be really clever here. The originalindex is a Map of Sets
           from original index. We want to reuse it as much as possible. If there
           was a guarantee that each element is present at at most one index we
           could reuse originalindex as it is. But there can be more, so we need to
           add remaining ones. Anyway we try to reuse old structure and keep
           new allocations low as much as possible.
         -}
        index' = case cast originalindex of
                   Just originalindex' ->
                       let dssf = filter (\(k,_v) -> not (Map.member k originalindex')) dss
                       in Ix.insertList dssf originalindex'
                   Nothing -> Ix.insertList dss index

-- | Inserts an item into the 'IxSet'. If your data happens to have
-- a primary key this function might not be what you want. See
-- 'updateIx'.
insert :: (Typeable a, Ord a,Indexable a) => a -> IxSet a -> IxSet a
insert = change Ix.insert

-- | Removes an item from the 'IxSet'.
delete :: (Typeable a, Ord a,Indexable a) => a -> IxSet a -> IxSet a
delete = change Ix.delete

-- | Will replace the item with index k.  Only works if there is at
-- most one item with that index in the 'IxSet'. Will not change
-- 'IxSet' if you have more then 1 item with given index.
updateIx :: (Indexable a, Ord a, Typeable a, Typeable k)
         => k -> a -> IxSet a -> IxSet a
updateIx i new ixset = insert new $
                     maybe ixset (flip delete ixset) $
                     getOne $ ixset @= i

-- | Will delete the item with index k.  Only works if there is at
-- most one item with that index in the 'IxSet'. Will not change
-- 'IxSet' if you have more then 1 item with given index.
deleteIx :: (Indexable a, Ord a, Typeable a, Typeable k)
         => k -> IxSet a -> IxSet a
deleteIx i ixset = maybe ixset (flip delete ixset) $
                       getOne $ ixset @= i

-- conversion operations

-- | Converts an 'IxSet' to a 'Set' of its elements.
toSet :: Ord a => IxSet a -> Set a
toSet (IxSet (Ix ix _:_)) = List.foldl' Set.union Set.empty (Map.elems ix)
toSet (IxSet []) = Set.empty

-- | Converts a 'Set' to an 'IxSet'.
fromSet :: (Indexable a, Ord a, Typeable a) => Set a -> IxSet a
fromSet = fromList . Set.toList

-- | Converts a list to an 'IxSet'.
fromList :: (Indexable a, Ord a, Typeable a) => [a] -> IxSet a
fromList list = insertList list empty

-- | Returns the number of unique items in the 'IxSet'.
size :: Ord a => IxSet a -> Int
size = Set.size . toSet

-- | Converts an 'IxSet' to its list of elements.
toList :: Ord a => IxSet a -> [a]
toList = Set.toList . toSet

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in ascending order by the index 'k'.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toAscList :: forall k a. (Indexable a, Typeable a, Typeable k) => Proxy k -> IxSet a -> [a]
toAscList _ ixset = concatMap snd (groupAscBy ixset :: [(k, [a])])

-- | Converts an 'IxSet' to its list of elements.
--
-- List will be sorted in descending order by the index 'k'.
--
-- The list may contain duplicate entries if a single value produces multiple keys.
toDescList :: forall k a. (Indexable a, Typeable a, Typeable k) => Proxy k -> IxSet a -> [a]
toDescList _ ixset = concatMap snd (groupDescBy ixset :: [(k, [a])])

-- | If the 'IxSet' is a singleton it will return the one item stored in it.
-- If 'IxSet' is empty or has many elements this function returns 'Nothing'.
getOne :: Ord a => IxSet a -> Maybe a
getOne ixset = case toList ixset of
                   [x] -> Just x
                   _   -> Nothing

-- | Like 'getOne' with a user-provided default.
getOneOr :: Ord a => a -> IxSet a -> a
getOneOr def = fromMaybe def . getOne

-- | Return 'True' if the 'IxSet' is empty, 'False' otherwise.
null :: IxSet a -> Bool
null (IxSet (Ix ix _:_)) = Map.null ix
null (IxSet [])          = True

-- set operations

-- | An infix 'intersection' operation.
(&&&) :: (Ord a, Typeable a, Indexable a) => IxSet a -> IxSet a -> IxSet a
(&&&) = intersection

-- | An infix 'union' operation.
(|||) :: (Ord a, Typeable a, Indexable a) => IxSet a -> IxSet a -> IxSet a
(|||) = union

infixr 5 &&&
infixr 5 |||

-- | Takes the union of the two 'IxSet's.
union :: (Ord a, Typeable a, Indexable a) => IxSet a -> IxSet a -> IxSet a
union (IxSet x1) (IxSet x2) = IxSet indexes'
    where
      indexes' = zipWith union' x1 x2
      union' (Ix a f) (Ix b _) =
          case cast b of
            Nothing -> error "IxSet.union: indexes out of order"
            Just b' -> Ix (Ix.union a b') f

-- | Takes the intersection of the two 'IxSet's.
intersection :: (Ord a, Typeable a, Indexable a) => IxSet a -> IxSet a -> IxSet a
intersection (IxSet x1) (IxSet x2) = IxSet indexes'
    where
      indexes' = zipWith intersection' x1 x2
      intersection' (Ix a f) (Ix b _) =
          case cast b of
            Nothing -> error "IxSet.intersection: indexes out of order"
            Just b' -> Ix (Ix.intersection a b') f


-- query operators

-- | Infix version of 'getEQ'.
(@=) :: (Indexable a, Typeable a, Ord a, Typeable k)
     => IxSet a -> k -> IxSet a
ix @= v = getEQ v ix

-- | Infix version of 'getLT'.
(@<) :: (Indexable a, Typeable a, Ord a, Typeable k)
     => IxSet a -> k -> IxSet a
ix @< v = getLT v ix

-- | Infix version of 'getGT'.
(@>) :: (Indexable a, Typeable a, Ord a, Typeable k)
     => IxSet a -> k -> IxSet a
ix @> v = getGT v ix

-- | Infix version of 'getLTE'.
(@<=) :: (Indexable a, Typeable a, Ord a, Typeable k)
      => IxSet a -> k -> IxSet a
ix @<= v = getLTE v ix

-- | Infix version of 'getGTE'.
(@>=) :: (Indexable a, Typeable a, Ord a, Typeable k)
      => IxSet a -> k -> IxSet a
ix @>= v = getGTE v ix

-- | Returns the subset with indexes in the open interval (k,k).
(@><) :: (Indexable a, Typeable a, Ord a, Typeable k)
      => IxSet a -> (k, k) -> IxSet a
ix @>< (v1,v2) = getLT v2 $ getGT v1 ix

-- | Returns the subset with indexes in [k,k).
(@>=<) :: (Indexable a, Typeable a, Ord a, Typeable k)
       => IxSet a -> (k, k) -> IxSet a
ix @>=< (v1,v2) = getLT v2 $ getGTE v1 ix

-- | Returns the subset with indexes in (k,k].
(@><=) :: (Indexable a, Typeable a, Ord a, Typeable k)
       => IxSet a -> (k, k) -> IxSet a
ix @><= (v1,v2) = getLTE v2 $ getGT v1 ix

-- | Returns the subset with indexes in [k,k].
(@>=<=) :: (Indexable a, Typeable a, Ord a, Typeable k)
        => IxSet a -> (k, k) -> IxSet a
ix @>=<= (v1,v2) = getLTE v2 $ getGTE v1 ix

-- | Creates the subset that has an index in the provided list.
(@+) :: (Indexable a, Typeable a, Ord a, Typeable k)
     => IxSet a -> [k] -> IxSet a
ix @+ list = List.foldl' union empty        $ map (ix @=) list

-- | Creates the subset that matches all the provided indexes.
(@*) :: (Indexable a, Typeable a, Ord a, Typeable k)
     => IxSet a -> [k] -> IxSet a
ix @* list = List.foldl' intersection ix $ map (ix @=) list

-- | Returns the subset with an index equal to the provided key.  The
-- set must be indexed over key type, doing otherwise results in
-- runtime error.
getEQ :: (Indexable a, Typeable a, Ord a, Typeable k)
      => k -> IxSet a -> IxSet a
getEQ = getOrd EQ

-- | Returns the subset with an index less than the provided key.  The
-- set must be indexed over key type, doing otherwise results in
-- runtime error.
getLT :: (Indexable a, Typeable a, Ord a, Typeable k)
      => k -> IxSet a -> IxSet a
getLT = getOrd LT

-- | Returns the subset with an index greater than the provided key.
-- The set must be indexed over key type, doing otherwise results in
-- runtime error.
getGT :: (Indexable a, Typeable a, Ord a, Typeable k)
      => k -> IxSet a -> IxSet a
getGT = getOrd GT

-- | Returns the subset with an index less than or equal to the
-- provided key.  The set must be indexed over key type, doing
-- otherwise results in runtime error.
getLTE :: (Indexable a, Typeable a, Ord a, Typeable k)
       => k -> IxSet a -> IxSet a
getLTE = getOrd2 True True False

-- | Returns the subset with an index greater than or equal to the
-- provided key.  The set must be indexed over key type, doing
-- otherwise results in runtime error.
getGTE :: (Indexable a, Typeable a, Ord a, Typeable k)
       => k -> IxSet a -> IxSet a
getGTE = getOrd2 False True True

-- | Returns the subset with an index within the interval provided.
-- The bottom of the interval is closed and the top is open,
-- i. e. [k1;k2).  The set must be indexed over key type, doing
-- otherwise results in runtime error.
getRange :: (Indexable a, Typeable k, Ord a, Typeable a)
         => k -> k -> IxSet a -> IxSet a
getRange k1 k2 ixset = getGTE k1 (getLT k2 ixset)

-- | Returns lists of elements paired with the indexes determined by
-- type inference.
groupBy :: (Typeable k,Typeable t) =>  IxSet t -> [(k, [t])]
groupBy (IxSet indexes) = collect indexes
    where
    collect [] = [] -- FIXME: should be an error
    collect (Ix index _:is) = maybe (collect is) f (cast index)
    f = map (second Set.toList) . Map.toList

-- | Returns lists of elements paired with the indexes determined by
-- type inference.
--
-- The resulting list will be sorted in ascending order by 'k'.
-- The values in '[t]' will be sorted in ascending order as well.
groupAscBy :: (Typeable k,Typeable t) =>  IxSet t -> [(k, [t])]
groupAscBy (IxSet indexes) = collect indexes
    where
    collect [] = [] -- FIXME: should be an error
    collect (Ix index _:is) = maybe (collect is) f (cast index)
    f = map (second Set.toAscList) . Map.toAscList

-- | Returns lists of elements paired with the indexes determined by
-- type inference.
--
-- The resulting list will be sorted in descending order by 'k'.
--
-- NOTE: The values in '[t]' are currently sorted in ascending
-- order. But this may change if someone bothers to add
-- 'Set.toDescList'. So do not rely on the sort order of '[t]'.
groupDescBy :: (Typeable k,Typeable t) =>  IxSet t -> [(k, [t])]
groupDescBy (IxSet indexes) = collect indexes
    where
    collect [] = [] -- FIXME: should be an error
    collect (Ix index _:is) = maybe (collect is) f (cast index)
    f = map (second Set.toAscList) . Map.toDescList

--query impl function

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.  The set must be indexed over key type,
-- doing otherwise results in runtime error.

getOrd :: (Indexable a, Ord a, Typeable a, Typeable k)
       => Ordering -> k -> IxSet a -> IxSet a
getOrd LT = getOrd2 True False False
getOrd EQ = getOrd2 False True False
getOrd GT = getOrd2 False False True

-- | A function for building up selectors on 'IxSet's.  Used in the
-- various get* functions.  The set must be indexed over key type,
-- doing otherwise results in runtime error.
getOrd2 :: (Indexable a, Ord a, Typeable a, Typeable k)
        => Bool -> Bool -> Bool -> k -> IxSet a -> IxSet a
getOrd2 inclt inceq incgt v ixset@(IxSet indexes) = collect indexes
    where
    collect [] = error $ "IxSet: there is no index " ++ showTypeOf v ++
                 " in " ++ showTypeOf ixset
    collect (Ix index _:is) = maybe (collect is) f $ cast v
        where
        f v'' = insertMapOfSets result empty
            where
            (lt',eq',gt') = Map.splitLookup v'' index
            ltgt = Map.unionWith Set.union lt gt
            result = case eq of
                       Just eqset -> Map.insertWith Set.union v'' eqset ltgt
                       Nothing -> ltgt
            lt = if inclt
                 then lt'
                 else Map.empty
            gt = if incgt
                 then gt'
                 else Map.empty
            eq = if inceq
                 then eq'
                 else Nothing

{--
Optimization todo:

* can we avoid rebuilding the collection every time we query?
  does laziness take care of everything?

* nicer operators?

* nice way to do updates that doesn't involve reinserting the entire data

* can we index on xpath rather than just type?

--}

instance (Indexable a, Typeable a, Ord a) => Monoid (IxSet a) where
    mempty = empty
    mappend = union

-- | Statistics about 'IxSet'. This function returns quadruple
-- consisting of 1. total number of elements in the set 2. number of
-- declared indexes 3. number of keys in all indexes 4. number of
-- values in all keys in all indexes. This can aid you in debugging
-- and optimisation.
stats :: (Ord a) => IxSet a -> (Int,Int,Int,Int)
stats (IxSet indexes) = (no_elements,no_indexes,no_keys,no_values)
    where
      no_elements = size (IxSet indexes)
      no_indexes = length indexes
      no_keys = sum [Map.size m | Ix m _ <- indexes]
      no_values = sum [sum [Set.size s | s <- Map.elems m] | Ix m _ <- indexes]


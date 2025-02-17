{-# LANGUAGE DeriveAnyClass, DeriveDataTypeable, DeriveGeneric, DerivingStrategies, FlexibleContexts, TemplateHaskell, UndecidableInstances, TemplateHaskell, DataKinds, FlexibleInstances, MultiParamTypeClasses, TypeOperators, KindSignatures #-}
{-# OPTIONS_GHC -fdefer-type-errors -fno-warn-orphans #-}

-- TODO (only if SYBWC is added again):
-- Check that the SYBWC Data instance for IxSet works, by testing
-- that going to and from XML works.

module Data.IxSet.Typed.Tests where

import           Prelude hiding (filter)
import           Control.Monad
import           Control.Exception
import           Data.Data         (Data, Typeable)
import           Data.IxSet.Typed  as IxSet
import           Data.Maybe
import qualified Data.Set          as Set
import           GHC.Generics      (Generic)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

data Foo
    = Foo String Int
      deriving stock (Eq, Generic, Ord, Show, Data, Typeable)
      deriving anyclass (CoArbitrary, Function)

data FooX
    = Foo1 String Int
    | Foo2 Int
      deriving (Eq, Ord, Show, Data, Typeable)

data NoIdxFoo
    = NoIdxFoo Int
      deriving (Eq, Ord, Show, Data, Typeable)

data BadlyIndexed
    = BadlyIndexed Int
      deriving (Eq, Ord, Show, Data, Typeable)

data MultiIndex
    = MultiIndex String Int Integer (Maybe Int) (Either Bool Char)
    | MultiIndexSubset Int Bool String
      deriving (Eq, Ord, Show, Data, Typeable)

data Triple
    = Triple Int Int Int
      deriving (Eq, Ord, Show, Data, Typeable)

data S
    = S String
      deriving (Eq, Ord, Show, Data, Typeable)

data G a b
    = G a b
      deriving (Eq, Ord, Show, Data, Typeable)

fooCalcs :: Foo -> String
fooCalcs (Foo s _) = s ++ "bar"

inferIxSet "FooXs"         ''FooX         'noCalcs  [''Int, ''String]
inferIxSet "BadlyIndexeds" ''BadlyIndexed 'noCalcs  [''String]
inferIxSet "MultiIndexed"  ''MultiIndex   'noCalcs  [''String, ''Int, ''Integer, ''Bool, ''Char]
inferIxSet "Triples"       ''Triple       'noCalcs  [''Int]
inferIxSet "Gs"            ''G            'noCalcs  [''Int]
inferIxSet "Foos"          ''Foo          'fooCalcs [''String, ''Int]

instance Indexable '[Int] S where
    indices = ixList (ixFun (\ (S x) -> [length x]))

ixSetCheckMethodsOnDefault :: TestTree
ixSetCheckMethodsOnDefault =
  testGroup "check methods on default" $
    [ testCase "size is zero" $
        0 @=? size (IxSet.empty :: Foos)
    , testCase "getOne returns Nothing" $
        Nothing @=? getOne (IxSet.empty :: Foos)
    , testCase "getOneOr returns default" $
        Foo1 "" 44 @=? getOneOr (Foo1 "" 44) (IxSet.empty :: FooXs)
    , testCase "toList returns []" $
        [] @=? toList (IxSet.empty :: Foos)
    ]

foox_a :: FooX
foox_a = Foo1 "abc" 10
foox_b :: FooX
foox_b = Foo1 "abc" 20
foox_c :: FooX
foox_c = Foo2 10
foox_d :: FooX
foox_d = Foo2 20
foox_e :: FooX
foox_e = Foo2 30

foox_set_abc :: FooXs
foox_set_abc = insert foox_a $ insert foox_b $ insert foox_c $ IxSet.empty
foox_set_cde :: FooXs
foox_set_cde = insert foox_e $ insert foox_d $ insert foox_c $ IxSet.empty

ixSetCheckSetMethods :: TestTree
ixSetCheckSetMethods =
  testGroup "check set methods" $
    [ testCase "size abc is 3" $
        3 @=? size foox_set_abc
    , testCase "size cde is 3" $
        3 @=? size foox_set_cde
    , testCase "getOne returns Nothing" $
        Nothing @=? getOne foox_set_abc
    , testCase "getOneOr returns default" $
        Foo1 "" 44 @=? getOneOr (Foo1 "" 44) foox_set_abc
    , testCase "toList returns 3 element list" $
        3 @=? length (toList foox_set_abc)
    ]

isError :: a -> Assertion
isError x = do
  r <- try (return $! x)
  case r of
    Left  (ErrorCall _) -> return ()
    Right _             -> assertFailure $ "Exception expected, but call was successful."

-- TODO: deferred type error checks disabled for now, because unfortunately, they are
-- fragile to test for throughout different GHC versions
badIndexSafeguard :: TestTree
badIndexSafeguard =
  testGroup "bad index safeguard" $
    [ -- TODO: the following is no longer an error. find a replacement test?
      -- testCase "check if there is error when no first index on value" $
      --   isError (size (insert (BadlyIndexed 123) empty :: BadlyIndexeds)) -- TODO: type sig now necessary
      -- TODO / GOOD: this is a type error now
      -- testCase "check if indexing with missing index" $
      --   isError (getOne (foox_set_cde @= True)) -- TODO: should actually verify it's a type error
    ]

testTriple :: TestTree
testTriple =
  testGroup "Triple"
    [ testCase "check if we can find element" $
        1 @=? size ((insert (Triple 1 2 3) empty :: Triples) -- TODO: type sig now necessary
                @= (1::Int) @= (2::Int))
    ]


instance Arbitrary Foo where
  arbitrary = liftM2 Foo arbitrary arbitrary

instance (Arbitrary a, Indexable (ix ': ixs) a)
           => Arbitrary (IxSet (ix ': ixs) a) where
  arbitrary = liftM fromList arbitrary

prop_sizeEqToListLength :: Foos -> Bool
prop_sizeEqToListLength ixset = size ixset == length (toList ixset)

sizeEqToListLength :: TestTree
sizeEqToListLength =
  testProperty "size === length . toList" $ prop_sizeEqToListLength

prop_union :: Foos -> Foos -> Bool
prop_union ixset1 ixset2 =
    toSet (ixset1 `union` ixset2) == toSet ixset1 `Set.union` toSet ixset2

prop_intersection :: Foos -> Foos -> Bool
prop_intersection ixset1 ixset2 =
    toSet (ixset1 `intersection` ixset2) ==
          toSet ixset1 `Set.intersection` toSet ixset2

prop_difference :: Foos -> Foos -> Bool
prop_difference ixset1 ixset2 =
    toSet (ixset1 `difference` ixset2) ==
          toSet ixset1 `Set.difference` toSet ixset2

prop_filter :: Fun Foo Bool -> Foos -> Bool
prop_filter p ixset =
    toSet (filter (applyFun p) ixset) ==
          Set.filter (applyFun p) (toSet ixset)

prop_any :: Foos -> [Int] -> Bool
prop_any ixset idxs =
    (ixset @+ idxs) == foldr union empty (map ((@=) ixset) idxs)

prop_all :: Foos -> [Int] -> Bool
prop_all ixset idxs =
    (ixset @* idxs) == foldr intersection ixset (map ((@=) ixset) idxs)

setOps :: TestTree
setOps = testGroup "set operations" $
  [ testProperty "distributivity toSet / union"        $ prop_union
  , testProperty "distributivity toSet / intersection" $ prop_intersection
  , testProperty "distributivity toSet / difference"   $ prop_difference
  , testProperty "distributivity toSet / filter"       $ prop_filter
  , testProperty "any (@+)"                            $ prop_any
  , testProperty "all (@*)"                            $ prop_all
  ]

prop_opers :: Foos -> Int -> Bool
prop_opers ixset intidx =
    and [ (lt `union` eq)            == lteq
        , (gt `union` eq)            == gteq
           -- this works for Foo as an Int field is in every Foo value
        , (gt `union` eq `union` lt) == ixset
--        , (neq `intersection` eq)    == empty
        ]
    where
--      neq  = ixset @/= intidx
      eq   = ixset @=  intidx
      lt   = ixset @<  intidx
      gt   = ixset @>  intidx
      lteq = ixset @<= intidx
      gteq = ixset @>= intidx

opers :: TestTree
opers = testProperty "query operators" $ prop_opers

prop_sureelem :: Foos -> Foo -> Bool
prop_sureelem ixset foo@(Foo _string intidx) =
    not (IxSet.null eq  ) &&
    not (IxSet.null lteq) &&
    not (IxSet.null gteq)
    where
      ixset' = insert foo ixset
      eq     = ixset' @=  intidx
      lteq   = ixset' @<= intidx
      gteq   = ixset' @>= intidx

sureelem :: TestTree
sureelem = testProperty "query / insert interaction" $ prop_sureelem

prop_ranges :: Foos -> Int -> Int -> Bool
prop_ranges ixset intidx1 intidx2 =
    ((ixset @><   (intidx1,intidx2)) == (gt1 &&& lt2)) &&
    ((ixset @>=<  (intidx1,intidx2)) == ((gt1 ||| eq1) &&& lt2)) &&
    ((ixset @><=  (intidx1,intidx2)) == (gt1 &&& (lt2 ||| eq2))) &&
    ((ixset @>=<= (intidx1,intidx2)) == ((gt1 ||| eq1) &&& (lt2 ||| eq2)))
    where
      eq1  = ixset @= intidx1
      _lt1 = ixset @< intidx1
      gt1  = ixset @> intidx1
      eq2  = ixset @= intidx2
      lt2  = ixset @< intidx2
      _gt2 = ixset @> intidx2

ranges :: TestTree
ranges = testProperty "ranges" $ prop_ranges

funSet :: IxSet '[Int] S
funSet = IxSet.fromList [S "", S "abc", S "def", S "abcde"]

funIndexes :: TestTree
funIndexes =
  testGroup "ixFun indices" $
    [ testCase "has zero length element" $
        1 @=? size (funSet @= (0 :: Int))
    , testCase "has two lengh 3 elements" $
        2 @=? size (funSet @= (3 :: Int))
    , testCase "has three lengh [3;7] elements" $
        3 @=? size (funSet @>=<= (3 :: Int, 7 :: Int))
    ]

bigSet :: Int -> MultiIndexed
bigSet n = fromList $
    [ MultiIndex string int integer maybe_int either_bool_char |
      string <- ["abc", "def", "ghi", "jkl"],
      int <- [1..n],
      integer <- [10000..10010],
      maybe_int <- [Nothing, Just 5, Just 6],
      either_bool_char <- [Left True, Left False, Right 'A', Right 'B']] ++
    [ MultiIndexSubset int bool string |
      string <- ["abc", "def", "ghi"],
      int <- [1..n],
      bool <- [True, False]]

findElementX :: MultiIndexed -> Int -> Bool
findElementX set n = isJust $ getOne (set @+ ["abc","def","ghi"]
                                      @>=<= (10000 :: Integer,10010 :: Integer)
                                      @= (True :: Bool)
                                      @= (n `div` n)
                                      @= "abc"
                                      @= (10000 :: Integer)
                                      @= (5 :: Int))

findElement :: Int -> Int -> Bool
findElement n m = all id ([findElementX set k | k <- [1..n]])
    where set = bigSet m

multiIndexed :: TestTree
multiIndexed =
  testGroup "MultiIndexed" $
    [ testCase "find an element" (True @=? findElement 1 1)
    ]

allTests :: TestTree
allTests =
  testGroup "ixset-typed tests" $
    [ testGroup "unit tests" $
      [ ixSetCheckMethodsOnDefault
      , ixSetCheckSetMethods
      , badIndexSafeguard
      , multiIndexed
      , testTriple
      , funIndexes
      ]
    , testGroup "properties" $
      [ sizeEqToListLength
      , setOps
      , opers
      , sureelem
      , ranges
      ]
    ]

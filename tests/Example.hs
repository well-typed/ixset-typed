{-# LANGUAGE DataKinds, MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable #-}
import Data.IxSet.Typed
import Data.Time
import Data.Int
import Data.Data
import Data.Typeable

-- Example from the documentation

data Entry = Entry Author [Author] Updated Id Content deriving (Show, Eq, Ord, Data, Typeable)
newtype Updated = Updated UTCTime                     deriving (Show, Eq, Ord, Data, Typeable)
newtype Id = Id Int64                                 deriving (Show, Eq, Ord, Data, Typeable)
newtype Content = Content String                      deriving (Show, Eq, Ord, Data, Typeable)
newtype Author = Author Email                         deriving (Show, Eq, Ord, Data, Typeable)
type Email = String

data Test = Test                                      deriving (Show, Eq, Ord, Data, Typeable)

type EntryIxs = '[Author, Id, Updated, Test, Word, FirstAuthor]
type IxEntry  = IxSet EntryIxs Entry

instance Indexable EntryIxs Entry where
  empty = mkEmpty
            (ixGen (Proxy :: Proxy Author))        -- out of order
            (ixGen (Proxy :: Proxy Id))
            (ixGen (Proxy :: Proxy Updated))
            (ixGen (Proxy :: Proxy Test))          -- bogus index
            (ixFun getWords)
            (ixFun getFirstAuthor)

entries  = insertList [e1, e2, e3, e4] (empty :: IxEntry)
entries1 = foldr delete entries [e1,e3]
entries2 = updateIx (Id 4) e5 entries

e1 = Entry (Author "abc@def.ghi")  [] (Updated t1) (Id 1) (Content "word1 word2")
e2 = Entry (Author "john@doe.com") [] (Updated t2) (Id 2) (Content "word2 word3")
e3 = Entry (Author "john@doe.com") [Author "abc@def.ghi"] (Updated t2) (Id 3) (Content "word1 word2 word3")
e4 = Entry (Author "abc@def.com") [Author "john@doe.com"] (Updated t3) (Id 4) (Content "word3")
e5 = Entry (Author "abc@def.com") [Author "john@doe.com"] (Updated t1) (Id 4) (Content "word1 word3 word4")
t1 = UTCTime (fromGregorian 2014 03 06) 0
t2 = UTCTime (fromGregorian 2012 12 12) 0
t3 = UTCTime (fromGregorian 1909 09 09) 0

entries3 = entries @= Author "john@doe.com" @< Updated t1

newtype Word = Word String                            deriving (Show)
newtype FirstAuthor = FirstAuthor Email               deriving (Show, Eq, Ord)

getWords (Entry _ _ _ _ (Content s)) = map Word $ words s
getFirstAuthor (Entry (Author author) _ _ _ _) = [FirstAuthor author]

entries4 = entries @+ [Word "word1", Word "word2"]
entries5 = entries @* [Word "word1", Word "word2"]
entries6 = entries @= FirstAuthor "john@doe.com"

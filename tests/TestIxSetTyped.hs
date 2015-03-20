module Main where

import Test.Tasty
import Data.IxSet.Typed.Tests (allTests)

main :: IO ()
main = defaultMain allTests

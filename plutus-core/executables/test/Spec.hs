-- | Unit tests for traceToStacks pure functions.

module Main (main) where

import           Test.Tasty (TestTree, defaultMain, testGroup)

getStacks_tests :: TestTree
getStacks_tests = testGroup "getStacks Tests" []

main :: IO ()
main = defaultMain getStacks_tests

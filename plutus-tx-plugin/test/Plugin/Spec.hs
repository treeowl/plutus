module Plugin.Spec where

import           Common

import           Plugin.Basic.Spec
import           Plugin.Data.Spec
import           Plugin.Errors.Spec
import           Plugin.Functions.Spec
import           Plugin.Laziness.Spec
import           Plugin.Primitives.Spec
import           Plugin.Profiling.Spec
import           Plugin.Typeclasses.Spec

tests :: TestNested
tests = testNested "Plugin" [
    basic
  , primitives
  , datat
  , functions
  , laziness
  , errors
  , typeclasses
  , profiling
  ]

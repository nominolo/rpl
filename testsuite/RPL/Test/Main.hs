module Main where

import qualified RPL.Test.Lexer ( tests )
import qualified RPL.Test.Supply ( tests )
import qualified RPL.Test.Typecheck ( tests )

import Test.Framework (defaultMain, testGroup)

tests = concat $ 
  [ RPL.Test.Lexer.tests
  , RPL.Test.Supply.tests
  , RPL.Test.Typecheck.tests
  ]

main = defaultMain tests

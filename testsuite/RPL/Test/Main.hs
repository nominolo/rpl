module Main where

import qualified RPL.Test.Lexer ( tests )
import qualified RPL.Test.Supply ( tests )

import Test.Framework (defaultMain, testGroup)

tests = concat $ 
  [ RPL.Test.Lexer.tests
  , RPL.Test.Supply.tests
  ]

main = defaultMain tests

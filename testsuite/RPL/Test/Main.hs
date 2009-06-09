module Main where

import qualified RPL.Test.Lexer ( tests )
import qualified RPL.Test.Parser ( tests )
import qualified RPL.Test.Supply ( tests )
import qualified RPL.Test.Typecheck ( tests )
import qualified RPL.Test.Utils ( tests )
import qualified RPL.Test.HMX ( tests )

import Test.Framework (defaultMain, Test)

tests :: [Test]
tests = concat $ 
  [ RPL.Test.Lexer.tests
  , RPL.Test.Parser.tests
  , RPL.Test.Supply.tests
  , RPL.Test.Typecheck.tests
  , RPL.Test.Utils.tests
  , RPL.Test.HMX.tests
  ]

main :: IO ()
main = defaultMain tests

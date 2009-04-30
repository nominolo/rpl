module Main where

import qualified RPL.Test.Lexer ( tests )

import Test.Framework (defaultMain, testGroup)

tests = RPL.Test.Lexer.tests

main = defaultMain tests

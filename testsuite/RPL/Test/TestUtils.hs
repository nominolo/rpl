module RPL.Test.TestUtils where

import Test.HUnit()

import qualified Data.ByteString.Lazy.Char8 as BS ()
import qualified Data.ByteString.Lazy.UTF8 as UTF8

stringInput :: String -> UTF8.ByteString
stringInput s = UTF8.fromString s



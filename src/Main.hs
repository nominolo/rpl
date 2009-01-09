module Main where

import RPL.Syntax
import qualified RPL.Lexer as L
import RPL.Parser
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

import qualified Data.ByteString.Lazy.Char8 as BS

main = do
  s <- BS.getContents
  let e = L.runParseM parseProgram s (startLoc "<stdin>")
  pprint e

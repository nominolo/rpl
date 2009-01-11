module Main where

import RPL.Syntax
import qualified RPL.Lexer as L
import RPL.Parser
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
import RPL.InferHMX

import qualified Data.ByteString.Lazy.Char8 as BS

main = do
  s <- BS.getContents
  let e = L.runParseM parseProgram s (startLoc "<stdin>")
  pprint e
  case e of
    Left _ -> return ()
    Right e' ->
      case runTcM (genConstraints [] e') of
        Left err -> pprint err
        Right (c, a) -> do
           pprint a
           pprint c
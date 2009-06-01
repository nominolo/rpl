module Main where

import RPL.Syntax
import qualified RPL.Lexer as L
import RPL.Parser
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
--import RPL.Typecheck.InferHMX
import RPL.Typecheck.AlgorithmW

import qualified Data.ByteString.Lazy.Char8 as BS

main = do
  s <- BS.getContents
  let e = L.runParseM parseProgram s (startLoc "<stdin>")
  pprint e
  case e of
    Left _ -> return ()
    Right e' -> do
      case runTcM (toplevelInfer e') of
        Left err -> pprint err
        Right r -> do
           debugPrint r
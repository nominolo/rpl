module Main where

-- import RPL.Syntax
-- import qualified RPL.Lexer as L
-- import RPL.Parser
-- import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
--import RPL.Typecheck.InferHMX
--import RPL.Typecheck.AlgorithmW

import RPL.Compiler
import RPL.Utils.Monads

import qualified Data.ByteString.Lazy.Char8 as BS

main = print =<< (runCompM defaultCompState $ do
  s <- io $ BS.getContents
  e <- parse "" s
  io $ pprint e
  r <- typecheck GraphicTypes e
  io $ debugPrint r)

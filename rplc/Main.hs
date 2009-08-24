module Main where

import RPL.Compiler
import RPL.Utils.Pretty
import RPL.Utils.Monads

import Data.List ( partition )
import System.Environment
import qualified Data.ByteString.Lazy.Char8 as BS
import Control.Applicative

parseOpts :: [String] -> ([String], [String])
parseOpts args = partition looks_like_flag args
    where
      looks_like_flag ('-':_) = True
      looks_like_flag _ = False

main :: IO ()
main = do
  (_flags, others) <- parseOpts `fmap` getArgs
  (src_name, s) 
      <- case others of
           [] -> (,) "stdin" <$> io BS.getContents
           (fn:_) -> (,) fn <$> io (BS.readFile fn)
  rslt <- runCompM defaultCompState $ do
            e <- parse src_name s
            io $ pprint e
            r <- typecheck GraphicTypes e
            io $ debugPrint r
  case rslt of
    Right _ -> return ()
    Left err -> do
      io $ pprint err

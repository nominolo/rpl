{-# LANGUAGE BangPatterns #-}
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

parseFlags :: [String] -> CompEnv -> CompEnv
parseFlags [] !env = env
parseFlags (f:fs) !env = parseFlags fs env'
  where
    env' =
      case f of
        "-ddump-final-graph" ->
          env{ solveOpts = (solveOpts env){ optDottyResult = True }}
        _ -> env

main :: IO ()
main = do
  (flags, others) <- parseOpts `fmap` getArgs
  (src_name, s)
      <- case others of
           [] -> (,) "stdin" <$> io BS.getContents
           (fn:_) -> (,) fn <$> io (BS.readFile fn)
  let env = parseFlags flags defaultCompEnv
  rslt <- runCompM env defaultCompState $ do
            env' <- ask
            io $ print (optDottyResult (solveOpts env'))
            e <- parse src_name s
            io $ pprint e
            r <- typecheck GraphicTypes e
            io $ pprint r
  case rslt of
    Right _ -> return ()
    Left err -> do
      io $ pprint err

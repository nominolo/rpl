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

parseFlags :: [String] -> (CompEnv, TcMode) -> (CompEnv, TcMode)
parseFlags [] !env = env
parseFlags (f:fs) (env, m) = parseFlags fs (env', m')
  where
    (env', m') =
      case f of
        "-ddump-final-graph" ->
          (env{ solveOpts = (solveOpts env){ optDottyResult = True }}, m)
        "-ddump-steps" ->
          (env{ solveOpts = (solveOpts env){ optDottySteps = True }}, m)
        "-ddump-initial-graph" ->
          (env{ solveOpts = (solveOpts env){ optDottyInitial = True }}, m)
        "-J" ->
          (env, AlgorithmJ)
        "-G" ->
          (env, GraphicTypes)
        "-W" ->
          (env, AlgorithmW)
        _ -> (env, m)

main :: IO ()
main = do
  (flags, others) <- parseOpts `fmap` getArgs
  (src_name, s)
      <- case others of
           [] -> (,) "stdin" <$> io BS.getContents
           (fn:_) -> (,) fn <$> io (BS.readFile fn)
  let (env, tc_mode) = parseFlags flags (defaultCompEnv, AlgorithmW)
  rslt <- runCompM env defaultCompState $ do
            env' <- ask
            io $ print (optDottyResult (solveOpts env'))
            e <- parse src_name s
            io $ pprint e
            r <- typecheck tc_mode e
            io $ pprint r
  case rslt of
    Right _ -> return ()
    Left err -> do
      io $ pprint err

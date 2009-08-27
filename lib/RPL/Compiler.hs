{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Main interface to the compiler.
module RPL.Compiler 
  ( CompEnv(..), SolveOpts(..), defaultCompEnv, defaultCompState,
    runCompM, CompM,
    parseFile, parse,
    typecheck, TcMode(..)
  )
where

import qualified RPL.Lexer as L
import RPL.Parser
import qualified RPL.Syntax as Syn
import RPL.Type
import RPL.Error
import RPL.Utils.SrcLoc
import RPL.Utils.Monads
import RPL.Typecheck.AlgorithmW
import RPL.Typecheck.Subst ( apply )
import RPL.Typecheck.GrTy

import qualified Data.ByteString.Lazy.Char8 as BS
import System.FilePath
import Control.Applicative

------------------------------------------------------------------------

data CompState = CompState

data CompEnv = CompEnv
  { solveOpts :: SolveOpts
  }

defaultCompEnv :: CompEnv
defaultCompEnv = CompEnv
  { solveOpts = defaultSolveOpts
  }

defaultCompState :: CompState
defaultCompState = CompState

newtype CompM a =
    CompM (ReaderT CompEnv (StrictStateErrorT CompState SourceError IO) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadError SourceError,
            MonadState CompState, MonadReader CompEnv)

runCompM :: CompEnv -> CompState -> CompM a -> IO (Either SourceError a)
runCompM env s0 (CompM act) = do
  r <- runStrictStateErrorT (runReaderT act env) s0
  case r of
    Left err -> return (Left err)
    Right (a, _) -> return (Right a)

parseFile :: FilePath -> CompM Syn.Program
parseFile fname = do
  -- TOOD: IO error handling
  parse fname =<< io (BS.readFile fname)

parse :: String -> BS.ByteString -> CompM Syn.Program
parse src_name src_code = do
  let rslt = L.runParseM parseProgram src_code (startLoc src_name)
  case rslt of
    Left err -> throwError err
    Right parsed -> return parsed
  
data TcMode
  = AlgorithmW
  | GraphicTypes

typecheck :: TcMode -> Syn.Expr -> CompM Type
typecheck AlgorithmW expr = do
  case runTcM (toplevelInfer expr) of
    Left err -> throwError err
    Right (subst, t) ->
        return (apply subst t)
typecheck GraphicTypes expr = do
  solveOpts_ <- asks solveOpts
  r <- liftIO $ tcExpr solveOpts_ MLF expr
  case r of
    Right t -> return t
    Left msg -> throwError (SourceError noSrcSpan (OtherError msg))

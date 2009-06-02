{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Typecheck.Monad (
  TcM, runTcM, IdGen(..), throwError, tcError,
  freshTyVar, freshSkolem,
  module Control.Applicative
) where

import RPL.Names
import RPL.Error
import RPL.Type
import RPL.Utils.Monads
import RPL.Utils.Unique
import RPL.Utils.SrcLoc ( SrcSpan )

import Data.Map ( Map )
import qualified Data.Map as M
import Control.Applicative

import Data.Supply

------------------------------------------------------------------------

class (Applicative m, Monad m) => IdGen m where genId :: String -> m Id

newtype TcM a = TcM { unTcM :: StrictStateErrorM (Int, Map String Int) SourceError a }
  deriving (Functor, Applicative, Monad)

runTcM :: TcM a -> Either SourceError a
runTcM m = runStrictStateErrorM (unTcM m) (100, M.empty)

instance IdGen TcM where genId = tcGenId

tcGenId :: String -> TcM Id
tcGenId disp_name =
    do (i, m) <- TcM getState
       let i' = i + 1
       let (n, m') = case M.lookup disp_name m of
             Nothing -> (disp_name, M.insert disp_name 1 m)
             Just o -> (disp_name ++ "_" ++ show o,
                        M.update (Just . (1+)) disp_name m)
       i' `seq` m' `seq` TcM (setState (i', m'))
       return $ Id (uniqueFromInt i) n

tcError :: SrcSpan -> ErrorMessage -> TcM a
tcError src msg = TcM $ throwError $ SourceError src msg

------------------------------------------------------------------------

freshSkolem :: IdGen m => Id -> m TyVar
freshSkolem n = mkSkolem <$> genId (idString n)

freshTyVar :: IdGen m => String -> m TyVar
freshTyVar = (mkTyVar `fmap`) . genId

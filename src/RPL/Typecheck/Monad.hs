module RPL.Typecheck.Monad where

import RPL.Names
import RPL.Error
import RPL.Utils.Monads

------------------------------------------------------------------------

type TcM a = StrictStateErrorM Int SourceError a

runTcM :: TcM a -> Either SourceError a
runTcM m = runStrictStateErrorM m 0

incCtr :: TcM Int
incCtr = do s <- getState; modifyState (+1); return s

genId :: String -> TcM Id
genId prefix = do i <- incCtr
                  return $ Id (prefix ++ show i)

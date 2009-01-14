module RPL.Typecheck.Monad where

import RPL.Names
import RPL.Error
import RPL.Utils.Monads
import RPL.Utils.Unique

------------------------------------------------------------------------

type TcM a = StrictStateErrorM Int SourceError a

runTcM :: TcM a -> Either SourceError a
runTcM m = runStrictStateErrorM m 100

incCtr :: TcM Int
incCtr = do s <- getState; modifyState (+1); return s

genId :: String -> TcM Id
genId disp_name =
    do i <- incCtr
       return $ Id (uniqueFromInt i) disp_name

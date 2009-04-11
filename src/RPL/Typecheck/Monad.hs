module RPL.Typecheck.Monad (
  TcM, runTcM, genId, throwError,
) where

import RPL.Names
import RPL.Error
import RPL.Type
import RPL.Utils.Monads
import RPL.Utils.Unique

import Data.Map ( Map )
import qualified Data.Map as M

------------------------------------------------------------------------

type TcM a = StrictStateErrorM (Int, Map String Int) SourceError a

runTcM :: TcM a -> Either SourceError a
runTcM m = runStrictStateErrorM m (100, M.empty)

genId :: String -> TcM Id
genId disp_name =
    do (i, m) <- getState
       let i' = i + 1
       let (n, m') = case M.lookup disp_name m of
             Nothing -> (disp_name, M.insert disp_name 1 m)
             Just o -> (disp_name ++ "_" ++ show o,
                        M.update (Just . (1+)) disp_name m)
       i' `seq` m' `seq` setState (i', m')
       return $ Id (uniqueFromInt i) n

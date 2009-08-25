-- | Clean up a type to display it to the user.
module RPL.Type.Tidy ( tidyType, basicNamesSupply ) where

import RPL.Type
import RPL.Names
import RPL.Utils.Unique ( uniqueFromInt )

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Supply
import System.IO.Unsafe ( unsafePerformIO )

-- Normalises names to @a@, @b@, ... from left to right.
tidyType :: Supply Id -> Type -> Type
tidyType names0 t0 = tidy names (env0 env0_names (S.toList (ftv t0))) t0
  where
    env0 _ [] = M.empty
    env0 ns (tv:tvs) =
      let (ns', tv_id) = split2 ns
          tv' = mkTyVar (supplyValue tv_id)
      in M.insert tv tv' (env0 ns' tvs)
    
    (env0_names, names) = split2 names0

    tidy _ env (TyVar tv) = TyVar (env M.! tv)
    tidy _ _ (TyCon tc) = TyCon tc
    tidy ns env (TyApp t1 t2) =
      let (ns2, ns1) = split2 ns in
      TyApp (tidy ns1 env t1) (tidy ns2 env t2)
    tidy ns env (TyAll tv ctxt t) =
      let (ns', ns_ctxt, tv_id) = split3 ns
          tv' = mkTyVar (supplyValue tv_id)
          env' = M.insert tv tv' env
          ctxt' = tidy_ctxt ns_ctxt env' ctxt
      in TyAll tv' ctxt' (tidy ns' env' t)

    tidy_ctxt _ _ BotCtxt = BotCtxt
    tidy_ctxt ns env (MLFCtxt is_rigid t) =
      MLFCtxt is_rigid (tidy ns env t)

basicNamesSupply :: Supply Id
basicNamesSupply = head `fmap` basicNamesSupply_

basicNamesSupply_ :: Supply [Id]
basicNamesSupply_ = unsafePerformIO $ newSupply names tail
  where
    names = zipWith Id (map uniqueFromInt [100..]) simpleNames

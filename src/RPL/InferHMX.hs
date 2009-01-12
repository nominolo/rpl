{-# LANGUAGE BangPatterns #-}
module RPL.InferHMX where

import RPL.Names
import RPL.Type
import RPL.Syntax
import RPL.Error
import RPL.Utils.Monads
import RPL.Utils.SrcLoc

import Control.Applicative

------------------------------------------------------------------------

type TcM a = StrictStateErrorM Int SourceError a

runTcM :: TcM a -> Either SourceError a
runTcM m = runStrictStateErrorM m 0

incCtr :: TcM Int
incCtr = do s <- getState; modifyState (+1); return s

genId :: String -> TcM Id
genId prefix = do i <- incCtr
                  return $ Id (prefix ++ show i)

------------------------------------------------------------------------

type Env = [(Id, TypeScheme)]

genConstraints :: Env -> Expr -> TcM (Constraint, Id)
genConstraints env (ELit _ lit) = do
    l <- genId "lit"
    let expected_type =
          case lit of
            IntLit _  -> TyCon (Id "Int") []
            CharLit _ -> TyCon (Id "Char") []
    return (TyVar l === expected_type, l)

--
--      x:(forall as. D => t) \in env    b fresh
--     ------------------------------------------
--       env ; x |- exists as. b === t /\ D # b
genConstraints env (EVar loc var) =
    case lookup var env of
      Nothing -> throwError (SourceError loc (NotInScope var))
      Just scheme -> do
        b <- genId (idString var)
        let d = tsConstaint scheme
        let t = tsType scheme
        let as = tsVars scheme
        return (mkExists as $ (TyVar b) === t /\ d, b)

-- 
--      env,x:a ; e  |-  ( C # c )            a, b fresh
--     --------------------------------------------------
--      env ; \x.e  |- exists a c. (b = a -> c /\ C) # b
--
genConstraints env (ELam _ (VarPat _ x) e) = do
    a <- genId (idString x)
    (cstr, c) <- genConstraints ((x, TsType (TyVar a)):env) e
    b <- genId "lam"
    return (mkExists [a,c] $ (TyVar b) === TyFun (TyVar a) (TyVar c) /\ cstr,
            b)

--
--      env ; e1 |- C1 # a1       env ; e2 |- C2 # a2       a fresh
--     -------------------------------------------------------------
--      env ; e1 e2 |- exists a1 a2. (C1 /\ C2 /\ a1 = a2 -> a) # a
--
genConstraints env (EApp _ e1 e2) = do
    a <- genId "app"
    (c1, a1) <- genConstraints env e1
    (c2, a2) <- genConstraints env e2
    return ( mkExists [a1, a2] $
               c1 /\ c2 /\ (TyVar a1) === TyFun (TyVar a2) (TyVar a)
           , a)

--
--      env ; e |- C1 # a   env,f:forall a.C1 => a ; e' |- C3 # b
--     -----------------------------------------------------------
--         env ; let f = e in e' |- (exists a . C1) /\ C3 # b
--
genConstraints env (ELet _ (VarPat _ f) e e') = do
    (c1, a) <- genConstraints env e
    (c3, b) <- genConstraints ((f, (TsQual [a] c1 (TyVar a))):env) e'
    return ( (mkExists [a] c1) /\ c3, b)

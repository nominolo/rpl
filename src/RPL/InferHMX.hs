{-# LANGUAGE BangPatterns, PatternGuards #-}
module RPL.InferHMX where

import RPL.Names
import RPL.Type
import RPL.Syntax
import RPL.Error
import RPL.Utils.Monads
import RPL.Utils.SrcLoc

import Control.Applicative
import Data.Monoid

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
--
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
    b <- genId "l_"
    return (mkExists [a,c] $ (TyVar b) === TyFun (TyVar a) (TyVar c) /\ cstr,
            b)

--
--      env ; e1 |- C1 # a1       env ; e2 |- C2 # a2       a fresh
--     -------------------------------------------------------------
--      env ; e1 e2 |- exists a1 a2. (C1 /\ C2 /\ a1 = a2 -> a) # a
--
genConstraints env (EApp _ e1 e2) = do
    a <- genId "a_"
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

------------------------------------------------------------------------

-- Normalised constraints have all "exists" qualifies at the top-level.
-- This can easily be achieved by renaming exists-bound variables.  Since
-- all variables are implicitly exists-bound, we drop the exists
-- alltogether.
normaliseConstr :: Constraint -> TcM Constraint
normaliseConstr c = norm c mempty

type FreeVars = [Id]
type Subst a b = [(a, b)]

--     x = y, (exists x z . x = y -> z), z = y -> x
--       ~~>
--     x = y, x1 = y -> z1, z -> y -> x

norm :: Constraint -> Subst Id Id -> TcM Constraint
norm c s0 =
  case c of
    CTrue ->
        return CTrue

    CEquals t1 t2 ->
        return (CEquals (normTerm s0 t1) (normTerm s0 t2))

    CAnd c1 c2 ->
        (/\) <$> norm c1 s0 <*> norm c2 s0

    CExists v c -> do
        v' <- genId (idString v ++ "_")
        let s' = (v, v') : s0
        norm c s' -- drop the exists, it's implicit at the top-level

normTerm :: Subst Id Id -> Term -> Term
normTerm s (TyCon c ts)   = TyCon c (map (normTerm s) ts)
normTerm s t@(TyVar v)
  | Just v' <- lookup v s = TyVar v'
  | otherwise             = t
normTerm s (TyFun t1 t2)  = TyFun (normTerm s t1) (normTerm s t2)

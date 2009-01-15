module RPL.Typecheck.AlgorithmW where

import Prelude hiding ( (!!) )

import RPL.Typecheck.Monad
import RPL.Typecheck.Subst

import RPL.Syntax
import RPL.Type
import RPL.Utils.Pretty
import RPL.BuiltIn
import RPL.Error

import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

------------------------------------------------------------------------

-- | Find the most general unifier of two types.
--
-- Returns either a substitution or the two types that failed to unify.
--
-- Does not perform an occurs-check.
unify :: Type -> Type -> Either (Type,Type) TySubst
unify (TyVar i) (TyVar j)
  | i == j                      = Right emptyTySubst
unify (TyCon c i) (TyCon c' i')
  | c == c' && i == i'          = Right emptyTySubst
unify (TyVar i) t               = Right (i |-> t)
unify t (TyVar i)               = Right (i |-> t)
unify (TyApp t1 t2) (TyApp t3 t4) =
    case unify t1 t3 of
      Right s ->
          case unify (apply s t2) (apply s t4) of
            Right s'           -> Right (s' `composeTySubst` s)
            err@(Left _)       -> err
      err@(Left _) -> err
unify t t'                      = Left (t,t')

------------------------------------------------------------------------
{-
t1 = let Right [a,b,c,d] = runTcM (mapM genId ["a","b","c","d"])
     in unify (mkFun [TyVar a, TyVar b]) (mkFun [typeInt, mkFun [TyVar c, TyVar d]])
-}
------------------------------------------------------------------------

-- | Turn a type into a type scheme abstracting over all free vars.
--
-- The first argument contains variables which should be treated as
-- monomorphic and should therefore *not* be quantified over.
--
-- Example (pseudo-syntax):
--
--     generalise {x} ((x -> y -> Int) -> z -> y)
--       == forall y z . (x -> y -> Int) -> z -> y
--
generalise :: Set Id -> Type -> TypeScheme
generalise monos t =
  mkForall (S.toList (ftv t `S.difference` monos)) CTrue t

-- | Infer the type of an expression in the top-level environment.
--
toplevelInfer :: Expr -> TcM (TySubst, Type)
toplevelInfer e = infer emptyTypeEnv e

-- | Infer the type of an expression using Algorithm W.
--
infer :: TypeEnv -> Expr -> TcM (TySubst, Type)
infer env (ELit _ l) =
    return (emptyTySubst, case l of
                            IntLit _ -> typeInt
                            CharLit _ -> typeChar)
infer env (EVar loc var) =
    case lookupTypeEnv env var of
      Nothing -> throwError (SourceError loc (NotInScope var))
      Just s -> do
        let as = tsVars s
        bs <- mapM (genId . idString) as
        return (emptyTySubst,
                apply (emptyTySubst // [ (a, TyVar b) | (a,b) <- zip as bs ])
                      (tsType s))

infer env (ELam _ (VarPat _ x) e) = do
    b <- genId (idString x)
    (s, t) <- infer (extendTypeEnv env x (mkForall [] CTrue (TyVar b))) e
    return (s, apply s (mkFun [TyVar b, t]))

infer env (EApp loc e1 e2) = do
    (s1, t1) <- infer env e1
    (s2, t2) <- infer (apply s1 env) e2
    b <- genId "t"
    case unify (apply s2 t1) (mkFun [t2, TyVar b]) of
      Left (t, t') -> throwError (SourceError loc (TypeMismatch (pretty t) (pretty t')))
      Right s3 ->
          return (s3 `composeTySubst` (s2 `composeTySubst` s1),
                  apply s3 (TyVar b))

infer env (ELet _ (VarPat _ x) e1 e2) = do
    (s1, t1) <- infer env e1
    let scheme = generalise (typeEnvDomain (apply s1 env)) t1
    (s2, t2) <- infer (extendTypeEnv (apply s1 env) x scheme) e2
    return (s2 `composeTySubst` s1, t2)

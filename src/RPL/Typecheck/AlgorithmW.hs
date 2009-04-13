module RPL.Typecheck.AlgorithmW
  ( module RPL.Typecheck.AlgorithmW
  , runTcM
  ) where

import Prelude hiding ( (!!) )

import RPL.Typecheck.Monad
import RPL.Typecheck.Subst
import RPL.Typecheck.Unify

import RPL.Syntax
import RPL.Type
import RPL.Utils.Pretty
import RPL.BuiltIn
import RPL.Error

import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List ( foldl' )

import Debug.Trace

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
generalise :: TypeEnv -> Type -> TypeScheme
generalise env t =
   mkForall (S.toList (ftv t `S.difference` monos)) [] t
  where
    -- free type vars in the type schemes of env
    monos = foldl' S.union S.empty (map tsFTV (envElems env))

-- | Infer the type of an expression in the top-level environment.
--
toplevelInfer :: Expr -> TcM (TySubst, Type)
toplevelInfer e = infer emptyEnv e


type TypeEnv = Env Id TypeScheme

-- | Infer the type of an expression using Algorithm W.
--
infer :: TypeEnv -> Expr -> TcM (TySubst, Type)
infer env (ELit _ l) =
    return (emptyTySubst, case l of
                            IntLit _ -> typeInt
                            CharLit _ -> typeChar)
infer env (EVar loc var) =
    case lookupEnv env var of
      Nothing -> throwError (SourceError loc (NotInScope var))
      Just s -> do
        let as = tsVars s
        bs <- mapM (freshTyVar . idString . tyVarId) as
        return (emptyTySubst,
                apply (emptyTySubst // [ (a, TyVar b) | (a,b) <- zip as bs ])
                      (tsType s))

infer env (ELam _ (VarPat _ x) e) = do
    b <- freshTyVar (idString x)
    (s, t) <- infer (extendEnv env x (mkForall [] [] (TyVar b))) e
    return (s, apply s (mkFun [TyVar b, t]))

infer env (EApp loc e1 e2) = do
    (s1, t1) <- infer env e1
    (s2, t2) <- infer (apply s1 env) e2
    b <- freshTyVar "t"
    case unify (apply s2 t1) (mkFun [t2, TyVar b]) of
      Left (t, t') -> throwError (SourceError loc (TypeMismatch (pretty t) (pretty t')))
      Right s3 ->
          return (s3 `composeTySubst` (s2 `composeTySubst` s1),
                  apply s3 (TyVar b))

infer env (ELet _ (VarPat _ x) e1 e2) = do
    (s1, t1) <- infer env e1
    let scheme = generalise (apply s1 env) t1
    (s2, t2) <- infer (extendEnv (apply s1 env) x scheme) e2
    return (s2 `composeTySubst` s1, t2)

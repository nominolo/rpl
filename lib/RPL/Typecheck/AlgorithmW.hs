module RPL.Typecheck.AlgorithmW
  ( module RPL.Typecheck.AlgorithmW
  , runTcM
  ) where

import Prelude hiding ( (!!) )

import RPL.Typecheck.Monad
import RPL.Typecheck.Subst
import RPL.Typecheck.Unify
import RPL.Typecheck.Utils

import RPL.Syntax hiding ( Type(..) )
import qualified RPL.Syntax as Syn
import RPL.Type
import RPL.Utils.Pretty
import RPL.Utils.SrcLoc
import RPL.BuiltIn
import RPL.Error

import qualified Data.Set as S
import Data.List ( foldl' )

------------------------------------------------------------------------

-- | Turn a type into a type scheme abstracting over all free vars.
--
-- The first argument contains variables which should be treated as
-- monomorphic and should therefore *not* be quantified over.
--
-- Example (pseudo-syntax):
--
-- > generalise {x} ((x -> y -> Int) -> z -> y)
-- >   == forall y z . (x -> y -> Int) -> z -> y
--
generalise :: S.Set TyVar -> Type -> TypeScheme
generalise monos t =
   mkForall (S.toList (ftv t `S.difference` monos)) [] t

-- | Infer the type of an expression in the top-level environment.
--
toplevelInfer :: Expr -> TcM (TySubst, Type)
toplevelInfer e = infer emptyEnv e

type TypeEnv = Env Id TypeScheme

freeTypeEnvVars :: TypeEnv -> S.Set TyVar
freeTypeEnvVars env = foldl' S.union S.empty (map tsFTV (envElems env))

-- | Infer the type of an expression using Algorithm W.
--
-- Think of the returned substitution as a set of equality constraints.
--
-- INVARIANT: TODO:
infer :: TypeEnv -> Expr -> TcM (TySubst, Type)
infer _env (ELit _ l) =
    return (emptyTySubst, litType l)

infer env (EVar loc var) = do
    scheme <- tcLookup env loc var
    (s, rho) <- instantiate scheme
    return (emptyTySubst, apply s rho)

infer env (ELam _ (VarPat _ x) e) = do
    b <- freshTyVar (idString x)
    (s, t) <- infer (extendEnv env x (mkForall [] [] (TyVar b))) e
    return (s, apply s (mkFun [TyVar b, t]))

infer env (EApp loc e1 e2) = do
    (s1, t1) <- infer env e1
    (s2, t2) <- infer (apply s1 env) e2
    b <- freshTyVar "t"
    case unify (apply s2 t1) (mkFun [t2, TyVar b]) of
      Left (t, t') -> tcError loc (TypeMismatch (pretty t) (pretty t'))
      Right s3 ->
          return (s3 `composeTySubst` (s2 `composeTySubst` s1),
                  apply s3 (TyVar b))

infer env (ELet _ (VarPat _ x) e1 e2) = do
    (s1, t1) <- infer env e1
    let scheme = generalise (freeTypeEnvVars $ apply s1 env) t1
    (s2, t2) <- infer (extendEnv (apply s1 env) x scheme) e2
    return (s2 `composeTySubst` s1, t2)

infer env (EAnn loc e ty) = do
    -- TODO: check for correctness
    (s1, t1) <- infer env e
    let most_general = generalise (freeTypeEnvVars $ apply s1 env) t1
    user_scheme <- fromUserType ty
    ok <- user_scheme `isInstanceOf` most_general
    if not ok then
      -- TODO: better error message
      -- TODO: print user's type annotation, not internal type
      tcError loc (TypeMismatch (pretty user_scheme) (pretty most_general))
     else do
      (s2, t2) <- instantiate user_scheme
      return (s1, apply s2 t2)

-- | Lookup a variable or throw not-in-scope error.
tcLookup :: TypeEnv -> SrcSpan -> Id -> TcM TypeScheme
tcLookup env loc var =
    case lookupEnv env var of
      Nothing -> tcError loc (NotInScope var)
      Just scheme -> return scheme

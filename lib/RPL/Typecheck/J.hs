{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Typecheck.J where

import RPL.Typecheck.Subst
import RPL.Typecheck.Unify hiding ( unify )
import RPL.Typecheck.Utils hiding ( instantiate )

import RPL.Type
import RPL.Type.Tidy
import RPL.Syntax hiding ( Type(..) )
import RPL.Error
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
--import RPL.BuiltIn
import RPL.Utils.Monads
import RPL.Utils.Unique

import qualified Data.Set as S
import Data.Supply
import Data.List ( foldl' )
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.Error
import Control.Monad.State

data JC = Uni Type Type

instance Pretty JC where
  ppr (Uni t1 t2) = ppr t1 <+> text "==" <+> ppr t2

data JState = JState
  { subst :: TySubst
  , freshs :: Supply Unique
  , constraints :: [(SrcSpan, JC)]
  }

emptyState :: JState
emptyState = JState emptyTySubst testSupply []

logConstr :: SrcSpan -> JC -> JM ()
logConstr loc ctrt =
  modify $ \st -> st { constraints = (loc, ctrt) : constraints st }

logDumb :: Expr -> JM Type -> JM Type
logDumb expr body =
  exists "*" $ \b -> do
  t <- body
  let loc = exprSpan expr
  -- TODO: really log *after* generating the body?
  unify loc (TyVar b) t
  return (TyVar b)

data JEnv = JEnv
  { gblEnv :: TypeEnv
  }

type TypeEnv = Env Id TypeScheme
type UVar = TyVar

newtype JM a = JM { unJM :: ReaderT JEnv (ErrorT SourceError (State JState)) a }
  deriving (Functor, Applicative, Monad,
            MonadState JState, MonadError SourceError, MonadReader JEnv)

testSupply :: Supply Unique
testSupply = unsafePerformIO newUniqueSupply
{-# NOINLINE testSupply #-}

runJM :: JM a -> Either SourceError a
runJM m = res
  where
    m1 = runReaderT (unJM m) (JEnv emptyEnv)
    m2 = runErrorT m1
    (res, _st) = runState m2 emptyState

tcProgram :: Expr -> JM Type
tcProgram e = do
  t <- tcExpr e
  s <- gets subst
  return $ tidyType basicNamesSupply $ apply s t

tcExpr :: Expr -> JM Type
tcExpr expr = logDumb expr $ tc_expr tcExpr expr

tc_expr :: (Expr -> JM Type) -> Expr -> JM Type
tc_expr _self (ELit _ lit) = do
  return (litType lit)

tc_expr _self (EVar loc x) = do
  scheme <- tcLookup loc x
  instantiate scheme

tc_expr self (ELam _ (VarPat loc x) e) =
  exists (idString x) $ \arg -> do
  let arg_t = TyVar arg
  t <- withLocalBinding loc x (mkForall [] [] arg_t) $ self e
  return (arg_t .->. t)

tc_expr self (EApp loc e1 e2) = do
  t1 <- self e1
  t2 <- self e2
  exists "@" $ \res -> do
  unify loc t1 (t2 .->. res)
  return (TyVar res)

tc_expr self (ELet _ (VarPat loc x) e1 e2) = do
  t1 <- self e1
  ts1 <- generalise t1
  withLocalBinding loc x ts1 $ do
    t2 <- tcExpr e2
    return t2

instantiate :: TypeScheme -> JM Type
instantiate (ForAll qtvs0 [] ty) = go emptyTySubst qtvs0
  where
    go !s [] = return $ apply s ty
    go !s (qtv:qtvs) = do
      exists "a" $ \qtv' -> go (addTySubstBinding s qtv (TyVar qtv')) qtvs

-- | Generalise type using the current environment and substitution.
generalise :: Type -> JM TypeScheme
generalise ty = do
  s <- gets subst
  env <- asks gblEnv
  -- FIXME: Make more efficient.  Idea 1: Only unification variables
  -- can be quantified over.
  return $ generalise' (freeTypeEnvVars (apply s env)) (apply s ty)

-- | Turn a type into a type scheme abstracting over all free vars.
-- 
-- The first argument contains variables which should be treated as
-- monomorphic and should therefore /not/ be quantified over.
-- 
-- Example (pseudo-syntax):
-- 
-- > generalise {x} ((x -> y -> Int) -> z -> y)
-- >   == forall y z . (x -> y -> Int) -> z -> y
-- 
generalise' :: S.Set TyVar -> Type -> TypeScheme
generalise' monos t =
   mkForall (S.toList (ftv t `S.difference` monos)) [] t


freeTypeEnvVars :: TypeEnv -> S.Set TyVar
freeTypeEnvVars env = foldl' S.union S.empty (map tsFTV (envElems env))


exists :: String -> (UVar -> JM a) -> JM a
exists nm body = do
  s <- gets freshs
  let (s1, s2) = split2 s
  let uvar = mkTyVar (mkId s1 (nm ++ show (intFromUnique (supplyValue s1))))
  modify $ \st -> st { freshs = s2 }
  body uvar

withLocalBinding :: SrcSpan -> Id -> TypeScheme -> JM a -> JM a
withLocalBinding _bind_site var ty_scheme body = do
  local (\env -> env { gblEnv = extendEnv (gblEnv env) var ty_scheme }) body

unify :: SrcSpan -> Type -> Type -> JM ()
unify site t1 t2 = do
  logConstr site (Uni t1 t2)
  s <- gets subst
  case unify2 s t1 t2 of
    Left (t, t') -> tcError site (TypeMismatch (pretty t) (pretty t'))
    Right s' -> modify $ \st -> st { subst = s' }

tcLookup :: SrcSpan -> Id -> JM TypeScheme
tcLookup loc var = do
  env <- asks gblEnv
  case lookupEnv env var of
    Nothing -> tcError loc (NotInScope var)
    Just s -> return s

tcError :: SrcSpan -> ErrorMessage -> JM a
tcError loc msg = throwError (SourceError loc msg)

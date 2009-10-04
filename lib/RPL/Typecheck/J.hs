{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Typecheck.J where

import RPL.Typecheck.Subst
import RPL.Typecheck.Env
import RPL.Typecheck.Unify hiding ( unify )
import RPL.Typecheck.Utils hiding ( instantiate )

import RPL.Type
import RPL.Type.Tidy
import RPL.Syntax hiding ( Type(..) )
import RPL.Error
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
import RPL.BuiltIn
import RPL.Utils.Monads
import RPL.Utils.Unique

import qualified Data.Set as S
import Data.Supply
import Data.List ( foldl', delete, unfoldr )
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.Error
import Control.Monad.State

data JC = Uni Type Type deriving Eq

instance Pretty JC where
  ppr (Uni t1 t2) = ppr t1 <+> text "==" <+> ppr t2

data JState = JState
  { subst :: TySubst
  , freshs :: Supply Unique
  , constraints :: [(SrcSpan, JC)]
  }

instance Pretty JState where
  ppr s = ppr (subst s)

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
  { gblEnv :: GlobalEnv
  , lclEnv :: LocalEnv
  }

type LocalEnv = Env Id Type
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
    m1 = runReaderT (unJM m) (JEnv emptyGlobalEnv emptyEnv)
    m2 = runErrorT m1
    (res, _st) = runState m2 emptyState

execJM :: JM a -> (Either SourceError a, JState)
execJM m = (res, st)
  where
    m1 = runReaderT (unJM m) (JEnv emptyGlobalEnv emptyEnv)
    m2 = runErrorT m1
    (res, st) = runState m2 emptyState


tcProgram :: GlobalEnv -> Expr -> JM Type
tcProgram gbl_env e =
  local (\_ -> JEnv gbl_env emptyEnv) $ do
    t <- tcExpr e
    s <- gets subst
    return $ tidyType basicNamesSupply $ apply s t

tcExpr :: Expr -> JM Type
tcExpr expr = do
--  callCC $ \k -> do   -- k :: Type -> JM Type a
  -- calling k 
  tc_expr tcExpr expr
--logDumb expr $ tc_expr tcExpr expr

tc_expr :: (Expr -> JM Type) -> Expr -> JM Type
tc_expr _self (ELit _ lit) = do
  return (litType lit)

tc_expr _self (EVar loc x) = do
  scheme <- tcLookup loc x
  instantiate scheme

tc_expr self (ELam _ (VarPat loc x) e) =
  exists (idString x) $ \arg -> do
  let arg_t = TyVar arg
  t <- extendLocalEnv loc x arg_t $
         self e
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
  extendGlobalEnv loc x ts1 $ do
    t2 <- self e2
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
  lcl_env <- asks lclEnv
  -- FIXME: Make more efficient.  Idea 1: Only unification variables
  -- can be quantified over.
  return $ generalise' (freeTypeEnvVars (apply s lcl_env)) (apply s ty)

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


freeTypeEnvVars :: LocalEnv -> S.Set TyVar
freeTypeEnvVars lcl_env =
  foldl' S.union S.empty (map ftv (envElems lcl_env))


exists :: String -> (UVar -> JM a) -> JM a
exists nm body = do
  s <- gets freshs
  let (s1, s2) = split2 s
  let uvar = mkTyVar (mkId s1 (nm ++ show (intFromUnique (supplyValue s1))))
  modify $ \st -> st { freshs = s2 }
  body uvar

extendGlobalEnv :: SrcSpan -> Id -> TypeScheme -> JM a -> JM a
extendGlobalEnv _bind_site var ty_scheme body = do
  local (\env -> env { gblEnv = extendNameEnv (gblEnv env) var ty_scheme }) body

extendLocalEnv :: SrcSpan -> Id -> Type -> JM a -> JM a
extendLocalEnv _bind_site var ty body =
  local (\env -> env { lclEnv = extendEnv (lclEnv env) var ty }) body

unify :: SrcSpan -> Type -> Type -> JM ()
unify site t1 t2 = do
  logConstr site (Uni t1 t2)
  s <- gets subst
  case unify2 s t1 t2 of
    Left (t, t') -> tcError site (TypeMismatch (pretty t) (pretty t'))
    Right s' -> modify $ \st -> st { subst = s' }

tcLookup :: SrcSpan -> Id -> JM TypeScheme
tcLookup loc var = do
  lcl_env <- asks lclEnv
  case lookupEnv lcl_env var of
    Just ty -> return (mkForall [] [] ty)
    Nothing -> do
      gbl_env <- asks gblEnv
      case lookupNameEnv gbl_env var of
        Just ty_scheme -> return ty_scheme
        Nothing -> tcError loc (NotInScope var)

tcError :: SrcSpan -> ErrorMessage -> JM a
tcError loc msg = throwError (SourceError loc msg)

----------------------------------------------------------------------

-- | Find /a/ minimal unsatisfiable subset of the input constraints.
-- 
-- Returns:
-- 
--  * @[]@ the input constraints are consistent.
-- 
--  * @s@ the input constraints are unsatisfiable and @s@ is a minimal
--    unsatisfiable set.  I.e., removing any element of @s@ makes it
--    satisfiable.
-- 
minUnsat :: [(SrcSpan, JC)] -> [(SrcSpan, JC)]
minUnsat cs0 = go emptyTySubst [] cs0
  where
    -- INVARIANT:
    --   constraintUnifier emptyTySubst min_approx == min_unif
    go min_unif min_approx not_tried =
      case constraintUnifier min_unif not_tried of
        Left c@(_, Uni t1 t2) ->
          -- c is in the minimal set; check whether adding @c@ would
          -- make the minimal set inconsistent
          case unify2 min_unif t1 t2 of
            Left _ ->
              -- yep, inconsistent.  We're done
              c : min_approx
            Right min_unif' ->
              go min_unif' (c : min_approx) (delete c not_tried)
        Right _ -> 
          -- adding all constraints succeeds => the input set was
          -- consistent
          []

-- | Find (most general) unifier for the given constraints.
-- 
-- Returns:
-- 
--  * @Right s <=>@ all constraints are consistent and @s@ is the most
--    general unifier.
-- 
--  * @Left c <=>@ constraints conflict and @c@ introduced the
--    conflict.  I.e., if the input constraints were:
-- 
--    > c_1, .., c_k, c_k+1, .., c_n
-- 
--    and the result is @Left c_k+1@, then the constraints @c_1, ..,
--    c_k@ were consistent, but adding @c_k+1@ introduced an
--    inconsistency.
-- 
constraintUnifier :: TySubst -> [(l, JC)] 
                  -> Either (l, JC) TySubst
constraintUnifier s [] = Right s
constraintUnifier s (c@(_, Uni t1 t2) : cs) =
  case unify2 s t1 t2 of
    Left _ -> Left c
    Right s' -> constraintUnifier s' cs



tst1 :: IO ()
tst1 = do
  s <- newUniqueSupply
  let locs = unfoldr (\l -> let l' = advanceSrcLoc l ' ' in
                            Just (mkSrcSpan l l', l'))
                     (startLoc "")
  let l1:l2:l3:l4:l5:l6:l7:_ = locs
  let names = zipWith mkId (split s) simpleNames
  let a:b:c:d:e:f:g:_ = map (TyVar . mkTyVar) names
  let tChar = TyCon typeChar
  let tInt = TyCon typeInt
  let cs = [ (l1, Uni a tChar), (l2, Uni b g), (l3, Uni e tInt),
             (l4, Uni f tInt), (l5, Uni g (e .->. f)),
             (l6, Uni b (a .->. c)), (l7, Uni c d) ]
  pprint $ minUnsat cs
  return ()

tc2 :: (Type -> JM b) -> (Expr -> JM Type) -> Expr -> JM b
tc2 k _ (ELit _ lit) = k (litType lit)
tc2 k _ (EVar loc x) = do
  scheme <- tcLookup loc x
  t <- instantiate scheme
  k t
tc2 k self (ELam _ (VarPat loc x) e) = do
  exists (idString x) $ \arg -> do
  let arg_t = TyVar arg
  t <- extendLocalEnv loc x arg_t $
         self e
  k (arg_t .->. t)
tc2 k self (EApp loc e1 e2) = do
  t1 <- self e1
  t2 <- self e2
  exists "@" $ \res -> do
  unify loc t1 (t2 .->. res)
  k (TyVar res)

tst2 :: String
tst2 = pretty $
  execJM $ do
    let mkdummy = (\_ -> exists "%" $ \b -> return (TyVar b))
    tc_expr mkdummy (EApp noSrcSpan undefined undefined)

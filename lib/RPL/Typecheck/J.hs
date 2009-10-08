{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Typecheck.J where

import RPL.Typecheck.Subst
import RPL.Typecheck.Env
import RPL.Typecheck.Unify hiding ( unify )
import RPL.Typecheck.Utils hiding ( instantiate )
import RPL.Typecheck.Minimise

import RPL.Type
import RPL.Type.Tidy
import RPL.Syntax hiding ( Type(..) )
import RPL.Error
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
import RPL.Utils.Monads
import RPL.Utils.Unique

import qualified Data.Set as S
import Data.Supply
import Data.List ( foldl' )
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.Error
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

data JC = Uni Type Type deriving Eq

instance Pretty JC where
  ppr (Uni t1 t2) = ppr t1 <+> text "==" <+> ppr t2

data JState = JState
  { subst :: TySubst
  , freshs :: Supply Unique
  }

instance Pretty JState where
  ppr s = ppr (subst s)

emptyState :: JState
emptyState = JState emptyTySubst testSupply

data JEnv = JEnv
  { extendGlobalEnvHook :: Id -> TypeScheme -> JM ()
  , extendLocalEnvHook :: Id -> Type -> JM ()
  , tcLookupHook :: Id -> JM TypeScheme -> JM TypeScheme
  , gblEnv :: GlobalEnv
  , lclEnv :: LocalEnv
  }

instance Pretty JEnv where
  ppr env = text "global:" <+> ppr (gblEnv env) $+$
            text "local: " <+> ppr (lclEnv env)

type LocalEnv = Env Id Type
type TypeEnv = Env Id TypeScheme
type UVar = TyVar

newtype JM a = JM { unJM :: ReaderT JEnv (ErrorT SourceError (State JState)) a }
  deriving (Functor, Applicative, Monad,
            MonadState JState, MonadError SourceError, MonadReader JEnv)

testSupply :: Supply Unique
testSupply = unsafePerformIO newUniqueSupply
{-# NOINLINE testSupply #-}

emptyJEnv :: JEnv
emptyJEnv = JEnv
  { extendGlobalEnvHook = \_ _ -> return ()
  , extendLocalEnvHook = \_ _ -> return ()
  , tcLookupHook = \_ k -> k
  , gblEnv = emptyGlobalEnv
  , lclEnv = emptyEnv
  }

runJM :: JM a -> Either SourceError a
runJM m = res
  where
    m1 = runReaderT (unJM m) emptyJEnv
    m2 = runErrorT m1
    (res, _st) = runState m2 emptyState

execJM :: JM a -> (Either SourceError a, JState)
execJM m = (res, st)
  where
    m1 = runReaderT (unJM m) emptyJEnv
    m2 = runErrorT m1
    (res, st) = runState m2 emptyState


tcProgram :: GlobalEnv -> Expr -> JM Type
tcProgram gbl_env e =
  local (\env -> env { gblEnv = gbl_env, lclEnv = emptyEnv }) $ do
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
tc_expr self (EWrap _ e) = self e

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

existsTy :: String -> (Type -> JM a) -> JM a
existsTy n k = exists n $ \v -> k (TyVar v)

existIds :: S.Set Id -> (M.Map Id Type -> JM a) -> JM a
existIds id_set k = do
  s <- gets freshs
  let ss = split s
      ids = S.toList id_set
      r = M.fromAscList $ 
           [ (i, TyVar (mkTyVar (mkId s ("t" ++ idString i))))
             | (s,i) <- zip ss ids ]
      s':_ = drop (M.size r) ss
  modify $ \st -> st { freshs = s' }
  k r

extendGlobalEnv :: SrcSpan -> Id -> TypeScheme -> JM a -> JM a
extendGlobalEnv _bind_site var ty_scheme body = do
  hook <- asks extendGlobalEnvHook
  hook var ty_scheme
  local (\env -> env { gblEnv = extendNameEnv (gblEnv env) var ty_scheme }) body

extendLocalEnv :: SrcSpan -> Id -> Type -> JM a -> JM a
extendLocalEnv _bind_site var ty body = do
  hook <- asks extendLocalEnvHook
  hook var ty
  local (\env -> env { lclEnv = extendEnv (lclEnv env) var ty }) body

extendLocalEnvN :: [(Id, Type)] -> JM a -> JM a
extendLocalEnvN [] m = m
extendLocalEnvN ((x,ty):binds) m =
  extendLocalEnv noSrcSpan x ty (extendLocalEnvN binds m)

unify :: SrcSpan -> Type -> Type -> JM ()
unify site t1 t2 = do
  s <- gets subst
  case unify2 s t1 t2 of
    Left (t, t') -> tcError site (TypeMismatch (pretty t) (pretty t'))
    Right s' -> modify $ \st -> st { subst = s' }

tcLookup :: SrcSpan -> Id -> JM TypeScheme
tcLookup loc var = do
  hook <- asks tcLookupHook
  hook var $ do
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

tst2 :: String
tst2 = pretty $
  execJM $ do
    let mkdummy = (\_ -> exists "%" $ \b -> return (TyVar b))
    tc_expr mkdummy (EApp noSrcSpan undefined undefined)

wrapAll :: Supply Int -> Expr -> Expr
wrapAll s_ e0 = go s_ e0
  where
    wrap s e = EWrap (supplyValue s) e
    go s e@(ELit _ _) = wrap s e
    go s e@(EVar _ _) = wrap s e
    go s (ELam l p e) =
        case split2 s of
          (s0, s1) -> wrap s0 (ELam l p (go s1 e))
    go s (EApp l e1 e2) =
        case split3 s of
          (s0, s1, s2) -> wrap s0 (EApp l (go s1 e1) (go s2 e2))
    go s (ELet l p e1 e2) =
        case split3 s of
          (s0, s1, s2) -> wrap s0 (ELet l p (go s1 e1) (go s2 e2))
    go s (EAnn l e t) =
        case split2 s of
          (s0, s1) -> wrap s0 (EAnn l (go s1 e) t)
    go s (EWrap _ e) = wrap s e  -- replace existing wraps

chop :: Supply Int -> Expr -> (Int, IM.IntMap Expr)
chop s_ e0 = go s_ e0
  where
    go s e@(ELit _ _) = let n = supplyValue s in (n, IM.singleton n e)
    go s e@(EVar _ _) = let n = supplyValue s in (n, IM.singleton n e)
    go s (ELam l p e) =
      case split2 s of
        (s0, s1) -> 
          let (ne, m) = go s1 e in
          let n = supplyValue s0 in
          (n, IM.insert n (ELam l p (hole ne)) m)
    go s (EApp l e1 e2) =
      case split3 s of
        (s0, s1, s2) ->
            let (ne1, m1) = go s1 e1
                (ne2, m2) = go s2 e2
                n = supplyValue s0
            in (n, IM.insert n (EApp l (hole ne1) (hole ne2)) (m1 `IM.union` m2))
    go s (ELet l p e1 e2) =
      case split3 s of
        (s0, s1, s2) ->
            let (ne1, m1) = go s1 e1
                (ne2, m2) = go s2 e2
                n = supplyValue s0
            in (n, IM.insert n (ELet l p (hole ne1) (hole ne2)) (m1 `IM.union` m2))
    go s (EAnn l e t) =
      case split2 s of
        (s0, s1) ->
          let (ne, m) = go s1 e in
          let n = supplyValue s0 in
          (n, IM.insert n (EAnn l (hole ne) t) m)
    go _ (EWrap _ _) = error "chop: unexpected EWrap"
    hole n = EWrap n (no_exp n)
    no_exp n = ELit noSrcSpan (IntLit n) --error "stripped expression"

----------------------------------------------------------------------

minimiseExpr :: Supply Int -> Supply Unique -> GlobalEnv -> Expr
             -> Expr
minimiseExpr s_wrap s_vars gbl_env expr0 =
    buildMinExpr chopped_expr_ minset top_expr
  where
    (top_expr, chopped_expr_) = chop s_wrap expr0
    chopped_expr = M.fromAscList (IM.toList chopped_expr_)
    minset_ = M.keysSet (minUnsat emptyState solve chopped_expr)
    minset = IS.fromAscList (S.toList minset_)
    my_env = emptyJEnv { tcLookupHook = my_tclookup
                       , gblEnv = gbl_env }
    my_tclookup _var kont =
      kont `catchError` (\_ -> 
        exists "$" $ \v -> do
        return (mkForall [v] [] (TyVar v)))

    all_cs = chopped_expr_
    tv_map = IM.fromAscList $ 
               [ (i, TyVar (mkTyVar (mkId s ("." ++ show i))))
                 | (i, s) <- zip (IM.keys all_cs) (split s_vars) ]
    
    solve s ci expr =
      let Just dummy_ty = IM.lookup ci tv_map in
      case stepJM my_env s (tc_one expr dummy_ty) of
        (Left err, _) -> Left err
        (Right _, s') -> Right s'

    tc_one expr ty = do
      (t, _free_vars) <- tcOne tv_map expr
      unify noSrcSpan t ty
      return t

tcOne :: IM.IntMap Type -> Expr -> JM (Type, M.Map Id (S.Set Type))
tcOne tv_map e_ = go e_
  where 
    go e@(EVar _ x) = do
      t <- tc_expr mkdummy e
      return (t, M.singleton x (S.singleton t))
    go e = do
      t <- tc_expr mkdummy e
      return (t, M.empty)

    mkdummy (EWrap n _) | Just t <- IM.lookup n tv_map = return t
    mkdummy _ = error "tcOne: no wrapper"

stepJM :: JEnv -> JState -> JM a -> (Either SourceError a, JState)
stepJM env st (JM m) = m3
  where
    m1 = runReaderT m env
    m2 = runErrorT m1
    m3 = runState m2 st

buildMinExpr :: IM.IntMap Expr -> IS.IntSet -> Int -> Expr
buildMinExpr pieces keep root = go (pieces IM.! root)
 where
   go e@(EVar _ _) = e
   go e@(ELit _ _) = e
   go (EApp l e1 e2) = EApp l (go e1) (go e2)
   go (ELam l x e1) = ELam l x (go e1)
   go (ELet l x e1 e2) = ELet l x (go e1) (go e2)
   go (EAnn l e t) = EAnn l (go e) t
   go (EWrap n _)
     | n `IS.member` keep =
         let Just e = IM.lookup n pieces in go e
     | otherwise = EVar noSrcSpan (mkId testSupply "..")

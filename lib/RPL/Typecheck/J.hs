{-# LANGUAGE PatternGuards #-}
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
    go s (EWrap _ _) = error "chop: unexpected EWrap"
    hole n = EWrap n (no_exp n)
    no_exp n = ELit noSrcSpan (IntLit n) --error "stripped expression"

--exprSet :: 

{-
tcExpr' :: GlobalEnv -> Expr -> JM Type
tcExpr' gbl_env expr = do
  local (\env -> env { tcLookupHook = my_tclookup
                     , extendLocalEnvHook = my_extendLocalEnv
                     , gblEnv = gbl_env }) $
    my_tcExpr expr

 where
   my_tclookup var _kont =
     exists "$" $ \v -> do
--      modify (\st -> st { assumpts = M.insertWith (S.union) var (S.singleton v)
--                                                  (assumpts st) })
     return (mkForall [v] [] (TyVar v))

   my_tcExpr e@(EVar _ var) = do
     t <- tc_expr my_tcExpr e
     modify (\st -> st { assumpts = M.insertWith (S.union) var (S.singleton t)
                                                 (assumpts st) })
     return t
   my_tcExpr e = tc_expr my_tcExpr e

   my_extendLocalEnv var ty = do
     as <- gets assumpts
     case M.lookup var as of
       Nothing -> return ()
       Just tys -> do
         forM_ (S.toList tys) $ \occ_ty -> do
           unify noSrcSpan ty occ_ty
-}

minimiseExpr :: Supply Int -> Supply Unique -> GlobalEnv -> Expr -> Expr
minimiseExpr s_wrap s_vars gbl_env expr0 = 
    buildMinExpr wrapped_expr minset top_expr
  where
    (top_expr, wrapped_expr) = chop s_wrap expr0
    minset = minUnsat' s_vars my_env wrapped_expr
    my_env = emptyJEnv { tcLookupHook = my_tclookup
                       , gblEnv = gbl_env }
    my_tclookup _var kont =
      kont `catchError` (\_ -> 
        exists "$" $ \v -> do
        return (mkForall [v] [] (TyVar v)))


minUnsat' :: Supply Unique -> JEnv -> IM.IntMap Expr -> IS.IntSet
minUnsat' suppl env all_cs = go emptyState IS.empty (IM.keysSet all_cs)
  where
    go min_state min_approx not_tried =
      case minTcParts env min_state all_cs tyvars not_tried of
        Left ci ->
          let Just c_expr = IM.lookup ci all_cs in
          let Just dummy_ty = IM.lookup ci tyvars in
          --trace ("adding " ++ show ci) $
          case stepJM env min_state (tc_one c_expr dummy_ty) of
            (Left _, _) ->
                IS.insert ci min_approx
            (Right _, s') ->
                go s' (IS.insert ci min_approx) (IS.delete ci not_tried)
        Right _ -> IS.empty

    tyvars = IM.fromAscList $ 
               [ (i, TyVar (mkTyVar (mkId s ("." ++ show i))))
                 | (i, s) <- zip (IM.keys all_cs) (split suppl) ]
    tc_one expr ty = do
      (t, _free_vars) <- tcOne tyvars expr
      unify noSrcSpan t ty
      return t

minTcParts :: JEnv -> JState -> IM.IntMap Expr -> IM.IntMap Type -> IS.IntSet -> Either Int JState
minTcParts env solver_state all_cs tyvars try_these = go solver_state try_these
  where
    --go s cs | trace (pretty (s, cs)) False = undefined
    go s cs =
      case IS.minView cs of
        Nothing -> Right s
        Just (ci, cs') ->
          let Just c_expr = IM.lookup ci all_cs in
          let Just dummy_ty = IM.lookup ci tyvars in
          case stepJM env s (tc_one c_expr dummy_ty) of
            (Left _, _) -> Left ci
            (Right _, s') -> go s' cs'
    tc_one expr ty = do
      (t, _free_vars) <- tcOne tyvars expr
      unify noSrcSpan t ty
      return t

tcOne :: IM.IntMap Type -> Expr -> JM (Type, M.Map Id (S.Set Type))
tcOne tv_map e = go e 
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

{-# LANGUAGE FlexibleContexts #-}
module RPL.Typecheck.Utils where

import Prelude hiding ( (!!) )

import RPL.Typecheck.Monad
import RPL.Typecheck.Subst

import RPL.Type
import RPL.Syntax hiding ( Type(..) )
import qualified RPL.Syntax as Syn
import RPL.BuiltIn
import RPL.Utils.Pretty
import RPL.Error
import Control.Monad.Error.Class

import Data.Maybe ( isJust )
import qualified Data.Set as S
import qualified Data.Map as M


litType :: Lit -> Type
litType (IntLit _) = TyCon typeInt
litType (CharLit _) = TyCon typeChar

fromUserType :: (Applicative m, MonadError SourceError m) =>
                Env Id TyCon -> Syn.Type -> m TypeScheme
fromUserType ty_env ty = do
    (vars, rho) <- outer ty 
    return $ ForAll (map mkTyVar vars) [] rho
  where
    outer (Syn.TAll _ v t) = do (vs, t') <- outer t; return (v:vs, t')
    outer t = do t' <- inner t; return ([], t')

    -- TODO: lookup the type constructor in the environment
    inner rho = case rho of
      Syn.TVar _ v    -> return $ TyVar (mkTyVar v)
      Syn.TCon s n    -> 
          case lookupEnv ty_env n of
            Just tc -> return $ TyCon tc
            Nothing -> unknown_tycon_error s n
      Syn.TApp _ t t' -> (@@) <$> inner t <*> inner t'
      Syn.TFun _ t t' -> (.->.) <$> inner t <*> inner t'
      Syn.TAll _s _v _t  ->
          throwError $ SourceError (typeSpan ty) $ WrongUserType $
            wrappingText "User type annotation contains nested foralls:" $$
            text "Full type annotation:" $$
            nest 4 (ppr ty) $$
            text "Offending part:" $$
            nest 4 (ppr rho)

    unknown_tycon_error s n = throwMsg s (NotInScope n)

-- | Instantiate a type scheme by substituting all forall-qualified
-- variables with fresh skolem variables.
--
-- Does not actually perform the substitution, but merely returns it.
instantiate :: IdGen m => TypeScheme -> m (TySubst, Type)
instantiate (ForAll vars [] ty) = do
  vars' <- mapM (freshSkolem . tyVarId) vars
  let s = tySubstFromList $ zip vars (map TyVar vars')
  return (s, ty)

-- | @x `isInstanceOf` y@ means \"@y@ is at least as general as @x@\".
--
-- For example:
--
-- > forall a. [a] -> [a]            `isInstanceOf`  forall a. a -> a
-- > forall b. (b -> b) -> (b -> b)  `isInstanceOf`  forall a. a -> a
-- > forall b. b -> b                `isInstanceOf`  forall a. a -> a
isInstanceOf :: IdGen m => TypeScheme -> TypeScheme -> m Bool
isInstanceOf ts1 ts2 = isJust <$> isInstanceOf' ts1 ts2

isInstanceOf' :: IdGen m => TypeScheme -> TypeScheme -> m (Maybe TySubst)
isInstanceOf' (ForAll tvs1 _ rho1) (ForAll tvs2 _ rho2) = do
    skolems <- mapM (freshSkolem . tyVarId) tvs1
    let subst = M.fromList (zip tvs1 skolems)
    let qualified_vars = S.fromList tvs2
    return $ go subst qualified_vars emptyTySubst rho1 rho2
  where
    go _skolems quals s t1 (TyVar v)
      | v `S.member` quals = 
          case s !! v of
            Nothing -> Just $ s // [(v, t1)]
            Just t' | t' == t1 -> Just s
                    | otherwise -> Nothing
    go _skolems _quals s t1@(TyVar _) (TyVar v) =
        Just $ s // [(v, t1)]
    go skolems quals s (TyApp t1 t2) (TyApp u1 u2) =
        do s' <- go skolems quals s t1 u1
           go skolems quals s' t2 u2
    go _skolems _quals s (TyCon tc1) (TyCon tc2)
      | tc1 == tc2 = Just s
    go _ _ _ _ _ = Nothing

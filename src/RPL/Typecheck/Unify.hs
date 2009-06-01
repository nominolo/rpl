{-# LANGUAGE PatternGuards #-}
module RPL.Typecheck.Unify where

import Prelude hiding ( (!!) )

import RPL.Typecheck.Subst
import RPL.Type

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

unify' :: Type -> Type -> Either (Type, Type) TySubst
unify' = unify2 emptyTySubst

unifyTypes :: [(Type, Type)] -> Either (Type, Type) TySubst
unifyTypes us0 = go emptyTySubst us0
  where
    go s [] = Right s
    go s ((t,t'):us) = case unify2 s t t' of
                         e@(Left _) -> e
                         Right s'   -> go s' us

-- TODO: kind checking
unify2 :: TySubst -> Type -> Type -> Either (Type, Type) TySubst
--unify2 subst t1 t2 | trace (pretty (subst, [t1, t2])) False = undefined 
unify2 subst (TyVar x) t = uVar subst x t
unify2 subst t (TyVar x) = uVar subst x t
unify2 subst (TyCon c i) (TyCon c' i')
  | c == c' && i == i'   = Right subst
unify2 subst (TyApp t1a t1b) (TyApp t2a t2b) =
   case unify2 subst t1a t2a of
     r@(Left _) -> r
     Right subst' -> unify2 subst' t1b t2b
unify2 _subst t1 t2      = Left (t1, t2)

uVar :: TySubst -> TyVar -> Type -> Either (Type, Type) TySubst
uVar subst x t | Just t' <- subst !! x =
   unify2 subst t' t
uVar subst x t = uUnrefined subst x t

uUnrefined :: TySubst -> TyVar -> Type -> Either (Type, Type) TySubst
uUnrefined subst x (TyVar x') 
  | x == x'               = Right subst
  | Just t' <- subst !! x' = uUnrefined subst x t'
uUnrefined subst x t =
  -- TODO: occurs check
  Right $ addTySubstBinding subst x t

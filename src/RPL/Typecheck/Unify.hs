module RPL.Typecheck.Unify where

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

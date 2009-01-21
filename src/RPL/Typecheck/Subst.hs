module RPL.Typecheck.Subst where

import RPL.Names
import RPL.Type

import RPL.Utils.Pretty

import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Monoid
import Data.List ( foldl' )

------------------------------------------------------------------------

newtype TySubst = TySubst (Map Id Type)

class HasTySubst a where
  apply :: TySubst -> a -> a

emptyTySubst :: TySubst
emptyTySubst = TySubst M.empty

-- | `composeTySubst s1 s2` first applies substitution `s2`, then on the
-- result applies substitution `s1`.  That is
--
--     apply (s1 `composeTySubst` s2) x == apply s1 (apply s2 x)
--
composeTySubst :: TySubst -> TySubst -> TySubst
composeTySubst s1@(TySubst m1) s2@(TySubst m2) =
   TySubst (M.map (apply s1) m2 `M.union` m1)
   -- XXX: M.union is left-biased, check that this here is correct

-- | Extend substitution.  Overwrites existing mappings.
(//) :: TySubst -> [(Id, Type)] -> TySubst
(TySubst s) // ab's = TySubst (M.union (M.fromList ab's) s)

(|->) :: Id -> Type -> TySubst
x |-> a = TySubst (M.singleton x a)

(!) :: TySubst -> Id -> Maybe Type
(TySubst m) ! x = M.lookup x m

delTySubst :: TySubst -> Id -> TySubst
delTySubst (TySubst m) x = TySubst (M.delete x m)

instance Monoid TySubst where
  mempty = emptyTySubst
  mappend = composeTySubst

instance Pretty TySubst where
  ppr (TySubst m) | M.null m = text "id"
                | otherwise = brackets (ppr_substs (M.toList m))
    where
      ppr_substs = fsep . punctuate comma .
                   map (\(v, t) -> ppr v <+> text ":=" <+> ppr t)

------------------------------------------------------------------------

instance HasTySubst Type where
  apply s t@(TyVar i) =
    case s ! i of
      Just t' -> t'
      Nothing -> t
  apply s t@(TyCon _ _) = t
  apply s (TyApp t1 t2) = TyApp (apply s t1) (apply s t2)

instance HasTySubst TypeScheme where
  apply s (TsType t) = TsType (apply s t)
  apply s (TsQual vs c t) =
      TsQual vs c (apply (foldl' delTySubst s vs) t)

------------------------------------------------------------------------

newtype Env t = Env (Map Id t)

emptyEnv :: Env t
emptyEnv = Env M.empty

lookupEnv :: Env t -> Id -> Maybe t
lookupEnv (Env m) x = M.lookup x m

extendEnv :: Env t -> Id -> t -> Env t
extendEnv (Env m) x ts = Env (M.insert x ts m)

envDomain :: Env t -> Set Id
envDomain (Env m) = M.keysSet m

instance HasTySubst t => HasTySubst (Env t) where
  apply s (Env m) = Env (M.map (apply s) m)

------------------------------------------------------------------------

prop_composeTySubst s1 s2 x =
   apply (s1 `composeTySubst` s2) x == apply s1 (apply s2 x)

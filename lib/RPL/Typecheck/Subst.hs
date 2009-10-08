{-# LANGUAGE FlexibleInstances #-}
module RPL.Typecheck.Subst where

import Prelude hiding ( (!!) )

import RPL.Typecheck.Monad
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

newtype TySubst = TySubst (Map TyVar Type)

instance Show TySubst where
  showsPrec _ (TySubst m) = showString "TySubst" . showsPrec 11 m

class HasTySubst a where
  apply :: TySubst -> a -> a

-- | The empty (identity) substitution.
emptyTySubst :: TySubst
emptyTySubst = TySubst M.empty

tySubstDomain :: TySubst -> Set TyVar
tySubstDomain (TySubst m) = M.keysSet m

tySubstFromList :: [(TyVar, Type)] -> TySubst
tySubstFromList =
    foldl' (\s (x,t) -> addTySubstBinding s x t) emptyTySubst

-- | `composeTySubst s1 s2` first applies substitution `s2`, then on the
-- result applies substitution `s1`.  That is
--
--     apply (s1 `composeTySubst` s2) x == apply s1 (apply s2 x)
--
composeTySubst :: TySubst -> TySubst -> TySubst
composeTySubst s1@(TySubst m1) (TySubst m2) =
   TySubst (m1 `M.union` M.map (apply s1) m2)

-- | Extend substitution.  Overwrites existing mappings.
(//) :: TySubst -> [(TyVar, Type)] -> TySubst
(TySubst s) // ab's = TySubst (M.union (M.fromList ab's) s)

(|->) :: TyVar -> Type -> TySubst
x |-> a = TySubst (M.singleton x a)

(!!) :: TySubst -> TyVar -> Maybe Type
(TySubst m) !! x = M.lookup x m

addTySubstBinding :: TySubst -> TyVar -> Type -> TySubst
addTySubstBinding (TySubst m) x t = TySubst (M.insert x t m)

-- | Delete a the mapping for a variable.
delTySubst :: TySubst -> TyVar -> TySubst
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

-- | Given an Id and a substitution returns the fully expanded type.
--
-- TODO: avoid infinite recursion
expandSubst :: TyVar -> TySubst -> Type
expandSubst x0 s = go (TyVar x0)
  where
    go (TyVar x) =
        case s !! x of
          Nothing -> TyVar x
          Just t' -> go t'
    go c@(TyCon _) = c
    go (TyApp t1 t2) = go t1 `TyApp` go t2

-- | Normalise type to use only easily distinguishable type variables.
--
-- For example:
--
--     forall t34 t45 tn9. (t34 -> t45) -> tn9 -> t34
--
-- becomes
--
--     forall a b c. (a -> b) -> c -> a
--
cleanUpForUser :: Type -> Type
cleanUpForUser ty = 
    let Right (ty',_,_) = runTcM $ go ty M.empty simpleNames in ty'
  where
    go (TyVar x) m ns =
       case M.lookup x m of
         Just x'  -> return (TyVar x', m, ns)
         Nothing -> do x' <- freshTyVar (head ns)
                       return (TyVar x', M.insert x x' m, tail ns)
    go c@(TyCon _) m ns = return (c, m, ns)
    go (TyApp t1 t2) m ns = do
        (t1', m', ns') <- go t1 m ns
        (t2', m'', ns'') <- go t2 m' ns'
        return (TyApp t1' t2', m'', ns'')

------------------------------------------------------------------------

instance HasTySubst Type where
  apply s t@(TyVar i) =
    case s !! i of
      Just t' -> apply s t'
      Nothing -> t
  apply _s t@(TyCon _) = t
  apply s (TyApp t1 t2) = TyApp (apply s t1) (apply s t2)

instance HasTySubst TypeScheme where
  apply s (ForAll vs c t) =
      ForAll vs c (apply (foldl' delTySubst s vs) t)

-- | Instantiate a type scheme to a monotype.  The substitution must be
-- defined for every forall-quantified variable of the type scheme.  The
-- result may contain skolems.
instantiate' :: TypeScheme -> TySubst -> Maybe Type
instantiate' (ForAll vs _c t) s@(TySubst m) =
    checkDomain vs >> return (apply s t)
  where checkDomain [] = Just ()
        checkDomain (v:vs') | v `M.member` m = checkDomain vs'
                            | otherwise      = Nothing

------------------------------------------------------------------------

newtype Env i t = Env (Map i t)

emptyEnv :: Env i t
emptyEnv = Env M.empty

singletonEnv :: Ord i => i -> t -> Env i t
singletonEnv x t = Env (M.singleton x t)

lookupEnv :: Ord i =>  Env i t -> i -> Maybe t
lookupEnv (Env m) x = M.lookup x m

extendEnv :: Ord i => Env i t -> i -> t -> Env i t
extendEnv (Env m) x ts = Env (M.insert x ts m)

extendEnvN :: Ord i => Env i t -> [(i,t)] -> Env i t
extendEnvN m ms = foldl' (\m' (i,t) -> extendEnv m' i t) m ms

envDomain :: Ord i => Env i t -> Set i
envDomain (Env m) = M.keysSet m

envElems :: Env i t -> [t]
envElems (Env m) = M.elems m

instance HasTySubst t => HasTySubst (Env i t) where
  apply s (Env m) = Env (M.map (apply s) m)

instance (Pretty i, Pretty t) => Pretty (Env i t) where
  ppr (Env m) = braces $ fsep . punctuate comma . map pp_one $ M.toList m
    where pp_one (i, t) = ppr i <+> colon <+> ppr t

------------------------------------------------------------------------

prop_composeTySubst :: (HasTySubst a, Eq a) =>
                       TySubst -> TySubst -> a -> Bool
prop_composeTySubst s1 s2 x =
   apply (s1 `composeTySubst` s2) x == apply s1 (apply s2 x)

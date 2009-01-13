module RPL.Type where

import RPL.Names
import RPL.Utils.Pretty

import Data.Set ( Set )
import qualified Data.Set as S

data Type
  = TyFun Type Type
  | TyVar Id
  | TyCon Id [Type]
  deriving (Eq, Show)

type Term = Type

data Constraint
  = CTrue
  | CEquals Term Term
  | CAnd Constraint Constraint
  | CExists Id Constraint
  deriving (Eq, Show)

------------------------------------------------------------------------
-- * Type Scheme

data TypeScheme
  = TsType Type
  | TsQual [Id] Constraint Type
  deriving (Eq, Show)

tsVars :: TypeScheme -> [Id]
tsVars (TsType _) = []
tsVars (TsQual vs _ _) = vs

tsConstaint :: TypeScheme -> Constraint
tsConstaint (TsType _) = CTrue
tsConstaint (TsQual _ c _) = c

tsType :: TypeScheme -> Type
tsType (TsType t) = t
tsType (TsQual _ _ t) = t

------------------------------------------------------------------------
-- * Helpers

-- ** Free Variables

-- | Free Type Variables.
ftv :: Type -> Set Id
ftv (TyVar v)     = S.singleton v
ftv (TyFun t1 t2) = S.union (ftv t1) (ftv t2)
ftv (TyCon _ ts)  = S.unions (map ftv ts)

-- | Free Type Variables of a type scheme.
tsFTV :: TypeScheme -> Set Id
tsFTV (TsType t)      = ftv t
tsFTV (TsQual vs _ t) = ftv t `S.difference` S.fromList vs

-- ** Constraint Construction

infixr 1 /\
infix 4 ===

(===) :: Term -> Term -> Constraint
t1 === t2 = CEquals t1 t2

(/\) :: Constraint -> Constraint -> Constraint
CTrue /\ c = c
c /\ CTrue = c
c1 /\ c2 = CAnd c1 c2

mkExists :: [Id] -> Constraint -> Constraint
mkExists vars c = foldr CExists c vars

------------------------------------------------------------------------
-- * Pretty Printing

instance Pretty Type where
  ppr typ = ppr_type typ

ppr_type (TyFun t1 t2) =
    parens (ppr t1 <+> sep (map ((text "->" <+>) . ppr) (ppr_fun_type t2)))
ppr_type (TyVar v) = ppr v
ppr_type (TyCon c ts) = 
    ppr c <+> sep (map ppr ts)

ppr_fun_type (TyFun t1 t2) = t1 : ppr_fun_type t2
ppr_fun_type t = [t]

-- t1 = pprint (TyFun (TyVar (Id "a")) 
--          (TyFun (TyFun (TyVar (Id "a")) (TyCon (Id "M") [TyVar (Id "b")]))
--                 (TyCon (Id "M") [TyVar (Id "a")])))

instance Pretty TypeScheme where
  ppr ts = ppr_type_scheme ts

ppr_type_scheme (TsType t) = ppr t
ppr_type_scheme (TsQual vs cs t) =
    sep [foralls, constraints, ppr t]
  where
    foralls = case vs of
                [] -> empty
                _ -> text "forall" <+> sep (map ppr vs) <+> char '.'
    constraints = case cs of
                    CTrue -> empty
                    _ -> ppr cs <+> text "=>"

instance Pretty Constraint where
  ppr = ppr_constraint

ppr_constraint CTrue = text "True"
ppr_constraint (CEquals t1 t2) = ppr t1 <+> text "=" <+> ppr t2
ppr_constraint (CAnd c1 c2) = sep [ppr c1 <> comma, ppr c2]
ppr_constraint (CExists v c) = ppr_exists c [v]

ppr_exists (CExists v c) vs = ppr_exists c (v:vs)
ppr_exists c vs = 
    parens $ hang (text "exists" <+> sep (map ppr (reverse vs)) <+> char '.')
               2 (ppr c)

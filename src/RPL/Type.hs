module RPL.Type where

import RPL.Names
import RPL.Utils.Pretty

data Type
  = TyFun Type Type
  | TyVar Id
  | TyCon Id [Type] 

type Term = Type

data Constraint
  = CTrue
  | CEquals Term Term
  | CAnd Constraint Constraint
  | CExists Id Constraint

------------------------------------------------------------------------
-- * Type Scheme

data TypeScheme
  = TsType Type
  | TsQual [Id] Constraint Type

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

infixr 1 /\
infix 4 ===

(===) :: Term -> Term -> Constraint
t1 === t2 = CEquals t1 t2

(/\) :: Constraint -> Constraint -> Constraint
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

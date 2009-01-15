module RPL.Type where

import RPL.Names
import RPL.Utils.Pretty
import RPL.Utils.Unique

import Data.Set ( Set )
import qualified Data.Set as S

-- Testing
import Test.QuickCheck

------------------------------------------------------------------------

data Type
  = TyVar Id
  | TyCon Id Int
  | TyApp Type Type
  deriving (Eq, Ord, Show)

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

mkForall :: [Id] -> Constraint -> Type -> TypeScheme
mkForall [] CTrue t = TsType t
mkForall vs c t = TsQual vs c t

------------------------------------------------------------------------
-- * Helpers

-- ** Type Construction

typeFun :: Type
typeFun = TyCon (Id (uniqueFromInt 3) "->") 2


--     x -> y -> z
--     == ((->) x ((->) y z))
--     == (((->) x) (((->) y) z))
--
--     x -> y == (((->) x) y)
mkFun :: [Type] -> Type
mkFun []     = error "mkFun: expects at least one argument"
mkFun [t]    = t
mkFun (t:ts) = TyApp (TyApp typeFun t) (mkFun ts)

-- ** Free Variables

-- | Free Type Variables.
ftv :: Type -> Set Id
ftv (TyVar v)     = S.singleton v
ftv (TyCon _ ts)  = S.empty
ftv (TyApp t1 t2) = S.union (ftv t1) (ftv t2)

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

ppr_type (TyVar v) = ppr v
ppr_type (TyCon c _) = ppr c
ppr_type (TyApp t t') 
  | t == typeFun = parens (ppr t' <+> ppr t)
  | otherwise    = parens $ ppr t <+> ppr t'

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

------------------------------------------------------------------------
-- * Testing

instance Arbitrary Type where
  arbitrary = sized $ \n ->
     if n < 3 then gen_node
              else gen_node_or_leaf n
    where
      gen_node =
          frequency
            [(2, TyVar `fmap` arbitrary)
            ,(1, do (Uppercase n) <- arbitrary
                    return (TyCon n 0))]
      gen_node_or_leaf n =
          frequency
            [(1,gen_node)
            ,(5,do t1 <- resize (n `div` 2) arbitrary
                   t2 <- resize (n `div` 2) arbitrary
                   return (mkFun [t1, t2]))]

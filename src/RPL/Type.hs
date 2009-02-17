{-# LANGUAGE TypeSynonymInstances #-}
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
  = TyVar TyVar
  | TyCon TyCon Int
  | TyApp Type Type
  deriving (Eq, Ord, Show)

type TyCon = Id  -- for now
type Term = Type
newtype TyVar = TV { tvId :: Id } deriving (Eq, Ord, Show)

mkTyVar :: Id -> TyVar
mkTyVar = TV

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
  | TsQual [TyVar] Constraint Type
  deriving (Eq, Show)

tsVars :: TypeScheme -> [TyVar]
tsVars (TsType _) = []
tsVars (TsQual vs _ _) = vs

tsConstaint :: TypeScheme -> Constraint
tsConstaint (TsType _) = CTrue
tsConstaint (TsQual _ c _) = c

tsType :: TypeScheme -> Type
tsType (TsType t) = t
tsType (TsQual _ _ t) = t

mkForall :: [TyVar] -> Constraint -> Type -> TypeScheme
mkForall [] CTrue t = TsType t
mkForall vs c t = TsQual vs c t

------------------------------------------------------------------------
-- * Helpers

-- ** Type Construction

-- | Type class to automatically lift arguments into types.
--
-- This class is used to allow writing a 'TyVar' where a 'Type' is expected.
-- 
class ToType a       where toType :: a -> Type
instance ToType Type  where toType = id
instance ToType TyVar where toType = TyVar

typeFun :: Type
typeFun = TyCon funTyCon 2

funTyCon :: TyCon
funTyCon = Id (uniqueFromInt 3) "->"

infixr 6 .->.

-- | Creates a function type.
(.->.) :: (ToType l, ToType r) => l -> r -> Type
l .->. r = TyApp (TyApp typeFun (toType l)) (toType r)

-- | Puts arrows between the list of types.
-- 
--     x -> y -> z
--     == ((->) x ((->) y z))
--     == (((->) x) (((->) y) z))
--
--     x -> y == (((->) x) y)
mkFun :: ToType t => [t] -> Type
mkFun []     = error "mkFun: expects at least one argument"
mkFun [t]    = toType t
mkFun (t:ts) = TyApp (TyApp typeFun (toType t)) (mkFun ts)

-- ** Free Variables

-- | Free Type Variables.
ftv :: Type -> Set TyVar
ftv (TyVar v)     = S.singleton v
ftv (TyCon _ ts)  = S.empty
ftv (TyApp t1 t2) = S.union (ftv t1) (ftv t2)

-- | Free Type Variables of a type scheme.
tsFTV :: TypeScheme -> Set TyVar
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

instance Pretty TyVar where
  ppr (TV x) = ppr x

instance Pretty Type where
  ppr typ = ppr_type typ

ppr_type t = ppr_type' 0 t

ppr_parens True d = parens d
ppr_parens False d = d

ppr_type' d (TyVar v) = ppr v
ppr_type' d (TyCon c _) = ppr c
ppr_type' d (TyApp (TyApp (TyCon c _) t) t')
  | isInfixTyCon c =
      let prec = infixTyConPrecedence c
          (prec_left, prec_right) =
              case infixTyConAssoc c of
                AssocLeft  -> (prec,     prec + 1)
                AssocRight -> (prec + 1, prec)
                AssocNone  -> (prec + 1, prec + 1)
      in ppr_parens (d > prec) $
        ppr_type' prec_left t <+> ppr c <+> ppr_type' prec_right t'
ppr_type' d (TyApp t t') =
    ppr_parens (d > 100) $ ppr_type' 100 t <+> ppr_type' 101 t'

-- | `True <=>` type constructor should be written infix instead of prefix.
isInfixTyCon :: TyCon -> Bool
isInfixTyCon c = c == funTyCon

-- | Return the precedence of an infix type constructor (a number between 0
-- and 100).  Type application has highest precedence (100), function arrow
-- has lowest precedence (0).
infixTyConPrecedence :: TyCon -> Int
infixTyConPrecedence _ = 0 -- function

infixTyConAssoc :: TyCon -> Associativity
infixTyConAssoc c | c == funTyCon = AssocRight
infixTyConAssoc _ = error "unknown associativity"


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
            [(2, TyVar `fmap` TV `fmap` arbitrary)
            ,(1, do (Uppercase n) <- arbitrary
                    return (TyCon n 0))]
      gen_node_or_leaf n =
          frequency
            [(1,gen_node)
            ,(5,do t1 <- resize (n `div` 2) arbitrary
                   t2 <- resize (n `div` 2) arbitrary
                   return (mkFun [t1 :: Type, t2]))]

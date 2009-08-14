{-# LANGUAGE TypeSynonymInstances #-}
module RPL.Type 
  ( -- * Types
    Type(..), Term, (.->.), mkFun, ftv, Ctxt(..)
  , -- * Type Constructors
    isInfixTyCon, tyConApp, TyCon(..), (@@)
    -- * Type Variables
  , TyVar, tyVarId, mkTyVar, mkSkolem, funTyCon
    -- * Constraints
  , Constraint, Constraints, (===), (/\)
    -- * Type Schemes
  , TypeScheme(..), tsVars, tsConstraints, tsType, mkForall, tsFTV
  )
where

import RPL.Names
import RPL.Utils.Pretty
import RPL.Utils.Unique

import Data.Set ( Set )
import qualified Data.Set as S
import Data.List ( foldl' )

-- Testing
import Test.QuickCheck

------------------------------------------------------------------------
-- * The Type of Types

-- | The Type of Types
data Type
  = TyVar TyVar
  | TyCon TyCon
  | TyApp Type Type
  | TyAll TyVar Ctxt Type
  deriving (Eq, Ord, Show)


data Ctxt = BotCtxt | MLFCtxt Bool Type
  deriving (Eq, Ord, Show)

data TyCon = MkTyCon 
  { tyConName :: Id
  , tyConArity :: Int
  } deriving (Eq, Ord, Show)

type Term = Type
data TyVar
  = -- | A user-named variable.
    TV { tyVarId :: Id }
  | Skolem { tyVarId :: Id }
  deriving (Eq, Ord, Show)

mkTyVar :: Id -> TyVar
mkTyVar = TV

mkSkolem :: Id -> TyVar
mkSkolem = Skolem

data Constraint
  = CEquals Term Term
  deriving (Eq, Show)

------------------------------------------------------------------------
-- * Type Scheme

data TypeScheme
  = ForAll [TyVar] Constraints Type
  deriving (Eq, Show)

type Constraints = [Constraint]

tsVars :: TypeScheme -> [TyVar]
tsVars (ForAll vs _ _) = vs

tsConstraints :: TypeScheme -> Constraints
tsConstraints (ForAll _ c _) = c

tsType :: TypeScheme -> Type
tsType (ForAll _ _ t) = t

mkForall :: [TyVar] -> Constraints -> Type -> TypeScheme
mkForall vs c t = ForAll vs c t

------------------------------------------------------------------------
-- * Helpers

-- ** Type Construction

-- | Type class to automatically lift arguments into types.
--
-- This class is used to allow writing a 'TyVar' where a 'Type' is expected.
-- 
class ToType a       where toType :: a -> Type
instance ToType Type
  where toType = id
instance ToType TyVar where toType = TyVar
instance ToType TyCon where toType = TyCon

typeFun :: Type
typeFun = TyCon funTyCon

funTyCon :: TyCon
funTyCon = MkTyCon (Id (uniqueFromInt 3) "->") 2

infixr 6 .->.
infixl 7 @@

(@@) :: (ToType a, ToType b) => a -> b -> Type
t1 @@ t2 = toType t1 `TyApp` toType t2

-- | Creates a function type.
(.->.) :: (ToType l, ToType r) => l -> r -> Type
l .->. r = TyApp (TyApp typeFun (toType l)) (toType r)

-- | Puts arrows between the list of types.
--
-- @
--     x -> y -> z
--     == ((->) x ((->) y z))
--     == (((->) x) (((->) y) z))
-- 
--     x -> y == (((->) x) y)
-- @
--
-- Input list must be non-empty.
mkFun :: ToType t => [t] -> Type
mkFun []     = error "mkFun: expects at least one argument"
mkFun [t]    = toType t
mkFun (t:ts) = TyApp (TyApp typeFun (toType t)) (mkFun ts)

tyConApp :: TyCon -> [Type] -> Type
tyConApp tcon args = foldl' TyApp (TyCon tcon) args

-- ** Free Variables

-- | Free Type Variables.
ftv :: Type -> Set TyVar
ftv (TyVar v)     = S.singleton v
ftv (TyCon _)     = S.empty
ftv (TyApp t1 t2) = S.union (ftv t1) (ftv t2)
ftv (TyAll tv ctxt t) = S.delete tv (ftv t `S.union` ctxtFTV ctxt)

ctxtFTV :: Ctxt -> Set TyVar
ctxtFTV BotCtxt = S.empty
ctxtFTV (MLFCtxt _ t) = ftv t

-- | Free Type Variables of a type scheme.
tsFTV :: TypeScheme -> Set TyVar
tsFTV (ForAll vs _ t) = ftv t `S.difference` S.fromList vs

-- ** Constraint Construction

infixr 1 /\
infix 4 ===

(===) :: Term -> Term -> Constraint
t1 === t2 = CEquals t1 t2

(/\) :: Constraints -> Constraints -> Constraints
[] /\ c = c
c /\ [] = c
c1 /\ c2 = c1 ++ c2

------------------------------------------------------------------------
-- * Pretty Printing

instance Pretty TyVar where
  ppr (TV x) = ppr x
  ppr (Skolem v) = text (idString v) <> char '_' <> ppr (idUnique v)

instance Pretty Type where
  ppr typ = ppr_type typ
instance Pretty TyCon where
  ppr (MkTyCon n _) = ppr n

ppr_type :: Type -> PDoc
ppr_type t = ppr_type' 0 t

ppr_parens :: Bool -> PDoc -> PDoc
ppr_parens True d = parens d
ppr_parens False d = d

ppr_type' :: Int -> Type -> PDoc
ppr_type' _ (TyVar v) = ppr v
ppr_type' _ (TyCon c) = ppr c
ppr_type' d (TyAll v c t) = ppr_parens (d > 0) $ ppr_forall [(v,c)] t
ppr_type' d (TyApp (TyApp (TyCon c) t) t')
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

ppr_forall :: [(TyVar, Ctxt)] -> Type -> PDoc
ppr_forall vs (TyAll v c t) = ppr_forall ((v,c):vs) t
ppr_forall vs t =
    text "forall" <+> sep (map ppr_ctxt (reverse vs)) <> char '.' <+>
    nest 2 (ppr_type' 0 t)
  where
    ppr_ctxt (v, BotCtxt) = ppr v
    ppr_ctxt (v, MLFCtxt rigid t') =
        parens $ ppr v <+> (if rigid then char '=' else char '>')
                       <+> ppr t'

-- | `True <=>` type constructor should be written infix instead of prefix.
isInfixTyCon :: TyCon -> Bool
isInfixTyCon c = c == funTyCon

-- | Return the precedence of an infix type constructor (a number between 0
-- and 100).  Type application has highest precedence (100), function arrow
-- has lowest precedence (0).
infixTyConPrecedence :: TyCon -> Int
infixTyConPrecedence _ = 1 -- function

infixTyConAssoc :: TyCon -> Associativity
infixTyConAssoc c | c == funTyCon = AssocRight
infixTyConAssoc _ = error "unknown associativity"


instance Pretty TypeScheme where
  ppr ts = ppr_type_scheme ts

ppr_type_scheme :: TypeScheme -> PDoc
ppr_type_scheme (ForAll [] [] t) = ppr t
ppr_type_scheme (ForAll vs cs t) =
    sep [foralls, constraints, ppr t]
  where
    foralls = case vs of
                [] -> empty
                _ -> text "forall" <+> sep (map ppr vs) <+> char '.'
    constraints = case cs of
                    [] -> empty
                    _ -> parens (fsep (map ppr cs)) <+> text "=>"

instance Pretty Constraint where
  ppr = ppr_constraint

ppr_constraint :: Constraint -> PDoc
ppr_constraint (CEquals t1 t2) = ppr t1 <+> text "=" <+> ppr t2

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
                    return (TyCon (MkTyCon n 0)))]
      gen_node_or_leaf n =
          frequency
            [(1,gen_node)
            ,(5,do t1 <- resize (n `div` 2) arbitrary
                   t2 <- resize (n `div` 2) arbitrary
                   return (mkFun [t1 :: Type, t2]))]

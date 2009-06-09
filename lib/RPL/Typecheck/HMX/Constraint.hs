{-# LANGUAGE TypeSynonymInstances #-}
module RPL.Typecheck.HMX.Constraint where

import RPL.Typecheck.HMX.Core
import RPL.Typecheck.MultiEquation

import RPL.Names
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

import qualified Data.Map as M
import qualified Data.Set as S

------------------------------------------------------------------------

newtype SchemeName = SName Id

instance Pretty SchemeName where ppr (SName n) = ppr n

data Constraint term var
  = CTrue SrcSpan
    -- ^ The trivial constraint.
  | Equals SrcSpan term term
    -- ^ Equality constraint (i.e., unification).
  | And [Constraint term var]
    -- ^ Conjunction of constraints.
  | Let [TypeScheme term var] (Constraint term var)
    -- ^ Generalises @let@ is more general  than @exists@ and @def@, so we
    -- combine them into one thing.
  | InstanceOf SrcSpan SchemeName term

-- | @ForAll loc rqs fqs c t@ represents a constraint language construct
-- of the form:
--
-- > forall rqs. exists fqs. [c] => t
--
-- @rqs@ are all rigid quantifiers, @fqs@ are all flexible quantifiers.
-- (Intuitively: For variables that are @forall@ quantified we must be able to
-- solve the constraints by picking an arbitrary element and then stick to
-- it.  Existentially bound variables are the things that we try to refine
-- by constraint solving.)
--
-- To model an @exists@ constraint, we simply set @rqs = []@.
data TypeScheme term var
  = ForAll { tsSpan :: SrcSpan
           , tsForalls :: [var]
           , tsExists  :: [var]
           , tsConstraint :: Constraint term var
           , tsTerms   :: M.Map String (term, SrcSpan)
           }

type TConstraint = Constraint CrTerm Var
type TScheme     = TypeScheme CrTerm Var

------------------------------------------------------------------------

infix 5 =?=

-- | Equality constraint.
(=?=) :: term -> term -> Constraint term var
t =?= t' = Equals noSrcSpan t t'

infix 5 <?
(<?) :: SchemeName -> term -> Constraint term var
n <? t = InstanceOf noSrcSpan n t

infixr 1 /\
(/\) :: Constraint term var -> Constraint term var -> Constraint term var
(CTrue _) /\ x         = x
x         /\ (CTrue _) = x
(And xs)  /\ (And ys)  = And (xs ++ ys)
(And xs)  /\ y         = And (y:xs)
x         /\ (And ys)  = And (x:ys)
x         /\ y         = And [x, y]

ex :: [Var] -> TConstraint -> TConstraint
ex vs c = Let [ForAll noSrcSpan [] vs c M.empty] (CTrue noSrcSpan)

forAll :: [Var] -> TConstraint -> TConstraint
forAll vs c = Let [ForAll noSrcSpan vs [] c M.empty] (CTrue noSrcSpan)

exists :: (CrTerm -> IO TConstraint) -> IO TConstraint
exists f = do
  var <- mkAnonVar Flexible
  c <- f (TVar var)
  return $ ex [var] c

--infix 5 .<=.
-- (.<=.) :: Id -> Type -> Constraint
-- (.<=.) = InstanceOf

true :: Constraint term var
true = CTrue noSrcSpan

scheme :: [Var] -> S.Set String
       -> (M.Map String (CrTerm, SrcSpan) -> IO TConstraint)
       -> IO TScheme
scheme vs names f = do
  (l, m) <- variableSet (const (Flexible, Nothing)) names
  c <- f m
  return $ ForAll noSrcSpan vs l c m

------------------------------------------------------------------------

instance Pretty TConstraint where
  ppr (CTrue _) = keyword "⊤"
  ppr (Equals _ t t') = ppr t <+> text "≡" <+> ppr t'
  ppr (And cs) = sep $ punctuate (text "∧") $ map ppr cs
  ppr (Let ss c) = keyword "let" <+> vcat (map ppr ss) <+> keyword "in" $$ ppr c
  ppr (InstanceOf _ sn t) = ppr sn <+> text "≤" <+> ppr t

instance Pretty TScheme where
  ppr (ForAll _ rqs fqs c _) =
      quant "∀" rqs <+> quant "∃" fqs <+> nest 2 (brackets (ppr c))
    where quant _ [] = empty
          quant q vs = keyword q <> (fsep $ map ppr vs) <> char '.'

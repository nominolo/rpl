{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Support for Multi-Equations
--
-- Multi-equations manage equations of the form:
--
-- > v1 = v2 = ... vn = C u1 .. un
--
-- or
--
-- > v1 = v2 = ... = vn
--
-- Here @v1, .., vn@ and @u1, .., un@ are only variables, never terms.  This
-- allows us to explicitly control sharing between substructures.  For
-- example, the term-level equality @a = C (D x) E = C (D b) c@ would be
-- expressed as the following set of multi-equations:
--
-- > a = C a1 a2
-- > a1 = D x
-- > x = b
-- > a2 = c = E
--
-- We can treat such a system as a type scheme by declaring some variables
-- as qualified variables.
--
-- TODO: Explain ranks.
-- 
module RPL.Typecheck.MultiEquation where

import Prelude hiding ( foldr )

import RPL.Typecheck.HMX.Core
import RPL.Utils.UnionFind as UF
import RPL.Utils.Pretty
import RPL.Utils.SrcLoc

import Data.Maybe ( isJust, fromMaybe )
import Control.Applicative
import System.IO.Unsafe ( unsafePerformIO ) -- for pretty printing IORef contents
import Data.Foldable
import Data.Traversable
import qualified Data.Set as S
import qualified Data.Map as M

------------------------------------------------------------------------

-- * IntRank

newtype IntRank = IntRank Int deriving (Eq, Ord, Show, Num)

instance Pretty IntRank where ppr (IntRank n) = int n

noRank :: IntRank
noRank = IntRank (-1)

outermost :: IntRank
outermost = IntRank 0

------------------------------------------------------------------------

-- * XXX: define these
type Mark = ()
noMark :: Mark
noMark = ()

newtype TName = TName String deriving (Eq, Ord)

instance Pretty TName where ppr (TName s) = text s


-- * Descriptor

type CrTerm = ArTerm Var

type Var = UF.Point Descriptor

-- | Describes a multi-equation (or, equivalence class).
--
-- If a multi-equation has no structure, it consists only of
-- variables.  If it has one, then all terms share the same structure.
-- For example, the following multi-equation has no structure:
--
-- > a = b = c
--
-- whereas this one has:
--
-- > a = b = C x
--
-- Note that a structure is always of depth 1; that is, a structure never
-- contains subterms, only variables (or constants).
--
-- The rank is used by the solver to quickly look up the definition site of
-- a variable.  The unifier only makes sure that when two multi-equations
-- are joined, the smaller rank is kept.
--
data Descriptor = MkDescr
  { descStruct :: Maybe Structure
      -- ^ The associated structure, see above.
  , descRank   :: {-# UNPACK #-} !IntRank
  , descKind   :: {-# UNPACK #-} !VarKind -- ^ See 'VarKind'
  , descMark   :: Mark
  , descName   :: Maybe TName
  , descPos    :: SrcSpan
  , descVar    :: Maybe Var
  }

-- | The structure of a descriptor.  See 'Descriptor'.
type Structure = Term Var

-- | Describes the \"rigidness\" of a variable.
data VarKind
  = Flexible -- ^ The variable can be unified with other terms
  | Rigid    -- ^ Cannot be unified.  Name given by user.
  | Constant -- ^ A constant, name given by user. TODO: verify this
  deriving (Eq)

instance Pretty VarKind where
  ppr Flexible = text "*"
  ppr Rigid    = text "+"
  ppr Constant = text "="

instance Pretty Descriptor where
  ppr d =
      ppr (descKind d) <> 
      (case descStruct d of
        Just s -> ppr s
        Nothing -> ppr (fromMaybe (TName "_") (descName d)))

instance Pretty a => Pretty (Point a) where
  ppr p = ppr (unsafePerformIO $ descriptor p)

------------------------------------------------------------------------

-- | Returns whether the variable is \"rigid\", i.e., cannot be unified with
-- other variables.
isRigid :: Var -> IO Bool
isRigid var = is_rigid <$> UF.descriptor var

is_rigid :: Descriptor -> Bool
is_rigid MkDescr{descKind=k} = k == Rigid || k == Constant

-- | Returns whether the variable is \"flexible\", i.e., can be unified with
-- other variables.
isFlexible :: Var -> IO Bool
isFlexible var = is_flexible <$> descriptor var

is_flexible :: Descriptor -> Bool
is_flexible MkDescr{descKind=k} = k == Flexible

-- | Return the name the variable.  Since the name comes from the descriptor
-- of the variable's equivalence class, the name may change when unifying
-- multi-equations.
varName :: Var -> IO (Maybe TName)
varName var = descName <$> UF.descriptor var

-- | Return the structure of the variable's equivalence class.
varStructure :: Var -> IO (Maybe Structure)
varStructure var = descStruct <$> UF.descriptor var

isStructured :: Var -> IO Bool
isStructured var = isJust <$> varStructure var

equivalent :: Var -> Var -> IO Bool
equivalent v1 v2 = UF.equivalent v1 v2

------------------------------------------------------------------------

mkAnonVar :: VarKind -> IO Var
mkAnonVar k = variable k Nothing Nothing noSrcSpan

mkVar :: VarKind -> String -> IO Var
mkVar k n = variable k (Just (TName n)) Nothing noSrcSpan

mkTermVar :: VarKind -> Structure -> IO Var
mkTermVar k s = variable k Nothing (Just s) noSrcSpan

variable :: VarKind -> Maybe TName -> Maybe Structure -> SrcSpan
         -> IO Var
variable kind name struct pos =
    UF.fresh (MkDescr { descStruct = struct
                      , descRank = noRank
                      , descMark = noMark
                      , descKind = kind
                      , descName = name
                      , descPos = pos
                      , descVar = Nothing
                      })

variableSet :: (TName -> (VarKind, Maybe TName)) 
            -> S.Set String
            -> IO ([Var], M.Map String (CrTerm, SrcSpan))
variableSet f s = do
  foldrM (\x (vs, xts) -> do
            let (k, n) = f (TName x)
            v <- variable k n Nothing noSrcSpan
            return (v:vs, M.insert x (TVar v, noSrcSpan) xts))
         ([], M.empty) s

data Pool = MkPool
  { poolRank :: {-# UNPACK #-} !IntRank
  , poolVars :: [Var]
  }

initialPool :: Pool
initialPool = MkPool outermost []

newPool :: Pool -> Pool
newPool (MkPool r _) = MkPool (r + 1) []

-- | Add variable to given pool.  Assumes the variable's rank has already
-- been set.
register :: Var -> Pool -> Pool
register v (MkPool r vs) = MkPool r (v:vs)

-- | Add variable to the pool and set the variables rank to the same as the
-- pool.
introduce :: Var -> Pool -> IO Pool
introduce v pool@(MkPool r _) = do
  UF.modifyDescriptor v (\d -> d { descRank = r })
  return $ register v pool

------------------------------------------------------------------------


chop :: Pool -> CrTerm -> IO (Pool, Var)
chop pool@(MkPool r vs0) term = do
    (vs, v) <- go [] term
    return (MkPool r (vs ++ vs0), v)
  where
    go acc (TVar v) = return (acc, v)
    go acc (TTerm (Var x)) = do
      (acc', x') <- go acc x
      v <- fresh' (Var x')
      return (v:acc', v)
    go acc (TTerm (App x y)) = do
      (acc', x') <- go acc x
      (acc'', y') <- go acc' y
      v <- fresh' (App x' y')
      return (v:acc'', v)
                               
    fresh' s =
      UF.fresh $ MkDescr { descStruct = Just s
                         , descRank   = r
                         , descMark   = noMark
                         , descKind   = Flexible
                         , descName   = Nothing
                         , descPos    = noSrcSpan
                         , descVar    = Nothing }
           

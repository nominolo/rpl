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
import RPL.Utils.Misc ( ifM )
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

-- | The result of unification; isomorphic to 'Maybe'.
data UnifyResult
    = Success
    | CannotUnify SrcSpan (ArTerm Var) (ArTerm Var)

instance Pretty UnifyResult where
  ppr Success = text "success"
  ppr (CannotUnify _ t1 t2) =
      text "Could not unify:" $+$
      nest 4 (ppr t1) $+$
      nest 4 (ppr t2)

-- Helper 
thenUnify :: IO UnifyResult -> IO UnifyResult -> IO UnifyResult
thenUnify m m' = do
  r <- m; case r of Success -> m'; _ -> return r

-- | Join the multi-equations associated with the two variables.
unifyVar :: SrcSpan -> Var -> Var -> IO UnifyResult
unifyVar pos0 var0_1 var0_2 = unify pos0 var0_1 var0_2
  where
    unify pos var1 var2 =
      ifM (not <$> UF.equivalent var1 var2)
        (unify' pos var1 var2)
        (return Success)

    unify' pos var1 var2 = do
      desc1 <- descriptor var1
      desc2 <- descriptor var2
      let new_kind 
            | is_rigid desc1 = descKind desc1
            | is_rigid desc2 = descKind desc2
            | otherwise      = Flexible
      let new_name =
              case (descName desc1, descName desc2) of
                (Just n1, Just n2)
                  | n1 /= n2 ->
                      if is_rigid desc1 then Just n1 else
                       if is_rigid desc2 then Just n2
                        else Nothing
                  | otherwise ->
                      Just n1
                (Just n, _) -> Just n
                (_, Just n) -> Just n
                _ -> Nothing
      let lower1 = descRank desc1 < descRank desc2

      -- merge1: Merge two multi-equations but keep the structure of the first
      -- merge2: Merge two multi-equations but keep the structure of the first
      let merge1 
           | lower1 = do
               UF.union var2 var1
               modifyDescriptor var1 $ \d -> d { descKind = new_kind
                                               , descName = new_name }
               return Success
           | otherwise = do
               UF.union var1 var2
               modifyDescriptor var2 $ \d -> d { descKind = new_kind
                                               , descName = new_name
                                               , descStruct = descStruct desc1 }
               return Success
      let merge2
           | lower1 = do
               UF.union var2 var1
               modifyDescriptor var1 $ \d -> d { descKind = new_kind
                                               , descName = new_name
                                               , descStruct = descStruct desc2 }
               return Success
           | otherwise = do
               UF.union var1 var2
               modifyDescriptor var2 $ \d -> d { descKind = new_kind
                                               , descName = new_name }
               return Success
      let merge | lower1    = merge1
                | otherwise = merge2
                 
      let fresh :: Maybe Structure -> IO Var
          fresh s = do
            UF.fresh (MkDescr
                      { descStruct = s
                      , descRank = descRank (if lower1 then desc1 else desc2)
                      , descMark = noMark
                      , descKind = new_kind
                      , descName = new_name
                      , descPos = noSrcSpan
                      , descVar = Nothing
                      })

      let filt v term = unify pos v =<< fresh (Just term)

      case (descStruct desc1, descStruct desc2) of
        -- neither multi-equation contains a term
        (Nothing, Nothing) | is_flexible desc1 && is_flexible desc2 -> merge
        (Nothing, _)       | is_flexible desc1                      -> merge2
        (_, Nothing)       | is_flexible desc2                      -> merge1

        -- exactly one multi-equation contains a term; keep that one
        (Just (Var v), _) -> unify pos v var2
        (_, Just (Var v)) -> unify pos v var1

        -- it's forbidden to unify rigid type variables with a structure
        (Nothing, _) -> -- var1 is rigid
          return $ CannotUnify pos (TVar var1) (TVar var2)
        (_, Nothing) -> -- var2 is rigid
          return $ CannotUnify pos (TVar var1) (TVar var2)
        
        -- We're trying to unify two compound terms.
        (Just (App l1 r1), Just (App l2 r2)) -> do
          merge
          unify pos l1 l2 `thenUnify` unify pos r1 r2


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
           

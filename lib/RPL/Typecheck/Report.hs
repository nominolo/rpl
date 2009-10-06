module RPL.Typecheck.Report where

import RPL.Typecheck.J ( tcExpr, unify, JM, stepJM, extendLocalEnv, exists )
import RPL.Typecheck.Minimise
import RPL.Syntax hiding ( Type(..) )
import RPL.Utils.Unique
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Monoid

data Chunk = Chunk 
  { chunkExpr :: Expr
  , subChunks :: S.Set Unique
  , chunkFreeVars :: S.Set Id
  , chunkBindsVars :: S.Set Id
  }

instance Pretty Chunk where
  ppr (Chunk e _ free_vars bound_vars) =
    ppr e <+>
    (if S.null bound_vars then empty else ppr bound_vars)

-- | Split expression into collection of one-level expressions.
-- 
-- A one-level expression does not contain any sub-expressions.  If an
-- expression has sub-expressions they get replaced by holes (written
-- @{n}@ where @n@ is the hole id).  Holes are represented simply by
-- (unique) variables.
-- 
-- Example (pseudo code):
-- 
-- > chop (\x -> (x 42)) ~~>
-- > {1: \x -> {2},  2: ({3} {4}),  3: x,  4: 42}
-- 
-- Chunks are annotated with their free and bound variables.  This is
-- used to detect dependencies between expressions.  E.g., whenever
-- chunk @3@ occurs in a slice, then so must @1@ since otherwise @x@
-- would become unbound.
-- 
chop :: Supply Unique
        -- ^ Used to generate hole IDs.  Uniques must be distinct from
        -- any variable occurring in the expression.
     -> Expr
     -> (Unique, M.Map Unique Chunk)
        -- ^ First argument is the ID assigned to the top-level
        -- expression.  Second includes all the chunks.
chop supply expr = go supply expr
 where
   wrap s k = let n = supplyValue s in (n, k n)
   none = S.empty
   one x = S.singleton x
   two x y = S.insert x (S.singleton y)
   hole u e =
     EVar (getSpan e)
          (mkId' u ("{" ++ show (intFromUnique u) ++ "}"))
   go s e@(ELit _ _) =
       wrap s (\n -> M.singleton n (Chunk e none none none))
   go s e@(EVar _ x) =
       wrap s (\n -> M.singleton n (Chunk e none (one x) none))
   go s (ELam l p@(VarPat _ x) e) =
     case split2 s of
       (s0, s1) ->
         let (n1, m) = go s1 e in
         wrap s0 $ \n -> 
           M.insert n (Chunk (ELam l p (hole n1 e)) (one n1)
                             none (one x))
                    m
   go s (EApp l e1 e2) =
     case split3 s of
       (s0, s1, s2) ->
         let (ne1, m1) = go s1 e1
             (ne2, m2) = go s2 e2
         in wrap s0 $ \n ->
              M.insert n (Chunk (EApp l (hole ne1 e1) (hole ne2 e2))
                                (two ne1 ne2) none none)
                       (m1 `M.union` m2)
   go s (ELet l p@(VarPat _ x) e1 e2) =
     case split3 s of
       (s0, s1, s2) ->
         let (ne1, m1) = go s1 e1
             (ne2, m2) = go s2 e2
         in wrap s0 $ \n ->
              M.insert n (Chunk (ELet l p (hole ne1 e1) (hole ne2 e2))
                                (two ne1 ne2) none (one x))
                       (m1 `M.union` m2)
   go s (EAnn l e t) =
     case split2 s of
       (s0, s1) ->
         let (n1, m) = go s1 e in
         wrap s0 $ \n ->
           M.insert n (Chunk (EAnn l (hole n1 e) t)
                             (one n1) none none)
                    m

-- * Minimal Slice

-- Finding the minimal type error slice uses the 'minUnsat' function
-- to 
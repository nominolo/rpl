{-# LANGUAGE BangPatterns #-}
module RPL.Typecheck.Report where

import RPL.Type
import RPL.Error
import RPL.Typecheck.Env
import RPL.Typecheck.J hiding ( chop )
import RPL.Typecheck.Minimise
import RPL.Syntax as Syn hiding ( Type(..) )
import RPL.Utils.Unique
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Reader
import Data.Maybe ( catMaybes )

--import Debug.Trace

data Chunk = Chunk 
  { chunkExpr :: Expr
  , subChunks :: [Id]
  , chunkFreeVars :: S.Set Id
  , chunkBindsVars :: S.Set Id
  }

-- Idea (a la Uniplate):
--   rebuild :: [Expr] -> Expr  -- rebuild
--   bindsVars :: [Id] then type will have form id_1 -> .. -> id_n -> t

instance Pretty Chunk where
  ppr (Chunk e _ _free_vars bound_vars) =
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
     -> (Id, M.Map Id Chunk)
        -- ^ First argument is the ID assigned to the top-level
        -- expression.  Second includes all the chunks.
chop supply expr = go supply expr
 where
   wrap s k = let !n = hole_id (supplyValue s) in (n, k n)
   none = S.empty
   one x = S.singleton x
   two x y = S.insert x (S.singleton y)
   hole u e =
     EVar (getSpan e) u
   hole_id u = (mkId' u ("_" ++ pretty u {- ++ ">" -}))

   go s e@(ELit _ _) =
       wrap s (\n -> M.singleton n (Chunk e [] none none))
   go s e@(EVar _ x) =
       wrap s (\n -> M.singleton n (Chunk e [] (one x) none))
   go s (ELam l p@(VarPat _ x) e) =
     case split2 s of
       (s0, s1) ->
         let (n1, m) = go s1 e in
         wrap s0 $ \n -> 
           M.insert n (Chunk (ELam l p (hole n1 e)) [n1]
                             none (one x))
                    m
   go s (EApp l e1 e2) =
     case split3 s of
       (s0, s1, s2) ->
         let (ne1, m1) = go s1 e1
             (ne2, m2) = go s2 e2
         in wrap s0 $ \n ->
              M.insert n (Chunk (EApp l (hole ne1 e1) (hole ne2 e2))
                                [ne1, ne2] none none)
                       (m1 `M.union` m2)
   go s (ELet l p@(VarPat _ x) e1 e2) =
     case split3 s of
       (s0, s1, s2) ->
         let (ne1, m1) = go s1 e1
             (ne2, m2) = go s2 e2
         in wrap s0 $ \n ->
              M.insert n (Chunk (ELet l p (hole ne1 e1) (hole ne2 e2))
                                [ne1, ne2] none (one x))
                       (m1 `M.union` m2)
   go s (EAnn l e t) =
     case split2 s of
       (s0, s1) ->
         let (n1, m) = go s1 e in
         wrap s0 $ \n ->
           M.insert n (Chunk (EAnn l (hole n1 e) t)
                             [n1] none none)
                    m

-- TODO: Is everything on the path to an element necessarily also in
-- the minimal slice? ==> NO

mkSlice :: Supply Unique -> (Id, M.Map Id Chunk) -> S.Set Id -> Expr
mkSlice supply (toplevel, chunks) keep =
  --trace (pretty (toplevel, chunks, keep)) $ 
   go_ toplevel
 where
   chunk_ids = M.keysSet chunks
   (s1, s2) = split2 supply

   -- We represent the empty slice by 'dotdot' and any non-empty slice
   -- by (dotdot_fn e_1 dotdot ... dotdot e_n dotdot).
   --
   -- Note the use of dotdot_fn so that we can distinguish slices from
   -- applications where the function doesn't matter, i.e.:
   --   (dotdot e_1 ...)
   dotFnSpan = unhelpfulSpan "dotdot_fn"
   dotdot = EVar (noSrcSpan) (mkId s1 "..")
   dotdot_fn = EVar dotFnSpan (mkId s2 "..")

   dots [] = dotdot
   dots es =
     let ilv [] = []
         ilv (x:xs) = x : dotdot : ilv xs
     in mkApp dotdot_fn (ilv es)

   --
   -- viewDots (dots xs) == xs
   --
   viewDots e@(EVar _ _)
     | e == dotdot = Just []
     | otherwise   = Nothing
   viewDots e@(EApp _ _ _) =
     let (f, args) = Syn.viewApp e in
     if f == dotdot_fn then
       let un_ilv (x:_:xs) = x : un_ilv xs
           un_ilv _ = []
       in Just (un_ilv args)
     else Nothing
   viewDots _ = Nothing

   go_ nid = go (EVar noSrcSpan nid)
   go e@(EVar _ n)
--     | trace (pretty n) False = undefined
     | n `S.member` chunk_ids =
        let Chunk expr sub_chunks _ _ = chunks M.! n in
        if n `S.member` keep then go expr
        else merge (map go_ sub_chunks)
     | otherwise = e
   go e@(ELit _ _) = e
   go (EApp l e1 e2) = EApp l (go e1) (go e2)
   go (ELam l x e1) = ELam l x (go e1)
   go (ELet l x e1 e2) = ELet l x (go e1) (go e2)
   go (EAnn l e t) = EAnn l (go e) t

   merge es0 = dots (merge' es0)
     where
       --merge' es | trace (pretty es) False = undefined
       merge' [] = []
       merge' (e:es) =
         case viewDots e of
           Nothing -> e : merge' es
           Just ds -> merge' ds ++ merge' es

-- * Minimal Slice

-- Finding the minimal type error slice uses the 'minUnsat' function
-- to 

data TcChunkState = TcChunkState
  { solverState :: JState
  , solverEnv   :: JEnv
  , holeTypes   :: M.Map Id Type
 -- , varTypes    :: M.Map Id Type
  }

instance Pretty TcChunkState where
  ppr (TcChunkState st env _ht) =
    char '<' <> (ppr st $+$ ppr env) <> char '>'

mkTcChunkState :: GlobalEnv -> M.Map Id Chunk -> JM TcChunkState
mkTcChunkState env0 chunks =
  local (\e -> e { gblEnv = env0 }) $ do
  existIds (M.keysSet chunks) $ \hole_tys ->
    extendLocalEnvN (M.toList hole_tys) $ do
      env <- ask
--      trace (pretty env) $
      return $ TcChunkState
        { solverState = emptyState
        , solverEnv = env
        , holeTypes = hole_tys
        }

tcChunk :: TcChunkState -> Id -> Chunk
        -> Either SourceError TcChunkState
--tcChunk cs chunk_id chunk | trace (pretty (underline (ppr chunk), cs)) False = undefined
tcChunk cs chunk_id chunk =
  case res of
    Left err -> Left err
    Right env ->
        Right (cs { solverState = s', solverEnv = env })
 where
    expr = chunkExpr chunk
    (res, s') =
        stepJM (solverEnv cs) (solverState cs) $ do
          ty <- tcExpr expr
          let Just c_ty = M.lookup chunk_id (holeTypes cs)
          unify (getSpan expr) ty c_ty
          case expr of
            -- See Note [Extracting Binder Types]
            ELam l (VarPat _ x) _ -> do
              existIds (S.singleton x) $ \m -> do
              let x_ty = m M.! x
              existsTy "r" $ \r -> do
              unify l ty (x_ty .->. r)
              extendLocalEnv l x x_ty $ ask
            _ -> ask

-- Note [Extracting Binder Types]
-- ------------------------------
--
-- If a chunk binds a local variable, it only gets bound inside the
-- chunk's holes.  If we want to avoid adding hooks into the type
-- checker (to extract the environment at certain points) we need to
-- find another way to get at the bindings.
--
-- For lambda expressions we can do it like this:
--
-- > \x -> {n} :: t
--
-- Type checking returns some type @t@, possibly a simple type
-- variable.  We know that it will be of function type, however, so
-- unifying it with a function type (of our choosing) must work:
--
-- > t == a -> b
--
-- We now also know that @x :: a@, so we add this fact to the local
-- (monomorphic) environment.
--
-- Polymorphic binding is a bit more difficult.  Manual quantification
-- might work, e.g.:
--
-- > let f = {1} in {2}
--
-- gets type checked as
--
-- > let f = {1} in (f, {2}) :: t == (t_f, t_2)
-- 
-- Then generalise @t_f@ and bind it to $f$ when type checking anything
-- inside hole ${2}$.  Seems messy, though.
--
-- Note: This all becomes less of an issue if there is a separate
-- function for type checking binders (i.e., patterns) that returns
-- all the variables that should be bound.  (In GHC these are
-- @tcLocalBinds@, @tcTopBinds@ and friends.)

-- | Produce a minimal failing program slice for the expression.
--
-- Examples:
--
-- > 7 8 9   ~~>  .. (7 ..) ..
-- 
-- The problem is that @7@ is used in a function position.  The
-- arguments don't matter.
--
-- In this next example, assume @Same :: a -> a -> a -> Same a@.
--
-- > Same 65 'a' 54   ~~>  Same .. 'a' 54
--
-- The problem is that two arguments are different.  In this example
-- there is another minimal slice:
--
-- > Same 65 'a' ..
--
-- An example with monomorphic binders:
-- 
-- > \x -> Pair (x 42) (x 'A')  ~~>  \x -> .. (x 42) .. (x 'A') ..
-- 
-- Removing any application of @x@ would remove the error type check.
-- Furthermore, if either of the arguments were changed, the program
-- would type check as well.  The fact that the applications occur
-- inside a @Pair@ is unimportant, however.
-- 
-- TODO: Handle let bindings.
-- 
minSlice :: Supply Unique -> GlobalEnv -> Expr -> JM Expr
minSlice supply env0 expr = do
  st <- mkTcChunkState env0 all_chunks
  let m = minUnsat' st tcChunk pick_next del all_chunks
  return $ mkSlice supply (top, all_chunks) (M.keysSet m)
 where
   (top, all_chunks) = chop supply expr

   __ = undefined

   binds = M.fromList
            [ (v, (hole_id, chk)) 
              | (hole_id, chk) <- M.toList all_chunks
              , v <- S.toList (chunkBindsVars chk) ]

   pick_next = pick_next' []
   pick_next' acc chunks =
     case M.minViewWithKey chunks of
       Nothing -> if null acc then Nothing else Just (acc, M.empty)
       Just ((hole_id, chunk), chunks') ->
         case S.toList (chunkFreeVars chunk) of
           [] -> Just ((hole_id, chunk):acc, chunks')
           vs ->
             let other_chunks =
                   catMaybes $ map (flip M.lookup binds) vs
             in Just (other_chunks ++ [(hole_id, chunk)], chunks')
   del [] cs = cs
   del ((k,_):ks) cs = M.delete k (del ks cs)

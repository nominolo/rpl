{-# LANGUAGE BangPatterns #-}
module RPL.Typecheck.Report where

import RPL.Type
import RPL.Error
import RPL.Typecheck.Env
import RPL.Typecheck.J
--import RPL.Typecheck.Minimise
import RPL.Syntax as Syn hiding ( Type(..) )
import RPL.Typecheck.Subst
import RPL.Utils.Unique
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

import qualified Data.Map as M
--import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.Error

import Debug.Trace

-- -------------------------------------------------------------------

-- Type checking a slice
--
-- x .. (mono var) make sure we have checked the chunk where x is
--      bound, grab x's associated tyvar @t_x@, and check this chunk
--      in the environment {x : t}
--
-- n | [] [] .. straightforward
--
-- \x -> [] .. typecheck and extract type of @x@
--
-- let f = []1 in []2
--
--   * Case (1):  f has a type annotation t.
--
--     When type checking []2 ore below bind f to t.  TODO: Perhaps also
--     try syntactic sub-types
--
--   * Case (2):  f has no type annotation.
--
--     Fully type check e1 (i.e., the full expression)
--
--      * Case (2a):  e1 does not type check.
--
--        Find and minimise error in e1, then bind f to forall a. a when
--        type checking e2
--
--      * Case (2b): e1 does type check
--
--        Record both type of e1 and chunks of []1.  Result type will
--        be the most general type in the appropriate context.
--
-- f .. occurence of polymorphic var.
--
--      If f has a type annotation just instantiate its type scheme.
--      If checking f's chunk fails just blame this occurrence.
--
--      If f has an associated expression, try to check it by assuming
--      the most general type first.  If this fails, then inline.
--

-- -------------------------------------------------------------------
-- * Chopping

__ :: a
__ = undefined

data Chunk = Chunk
  { chunkExpr :: Expr
  , chunkDepends :: [ChunkId]
  , chunkHoles :: [ChunkId]
  , rebuild :: [Expr] -> Expr
  , tcChunk :: JEnv -> JState -> TcChunkResult
  }

instance Pretty Chunk where
  ppr ch = ppr (chunkExpr ch) <+>
           (if null (chunkDepends ch) then empty else ppr (chunkDepends ch))
  
type ChunkId = Id
type Chunks = M.Map ChunkId Chunk

inline :: Chunk -> Chunk
inline = __

data TcChunkResult
  = TcFail SourceError
  | TcOk JState Type (JEnv -> JEnv)

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
-- TODO: MOAR D-TAIL!!11
chop :: Supply Unique -> Expr -> (ChunkId, Chunks)
chop us0 expr = go us0 env0 expr
  where
   env0 = emptyEnv
   hole_id u = (mkId' u ("_" ++ pretty u {- ++ ">" -}))
   hole u e = EVar (getSpan e) u

   wrap s k = let !n = hole_id (supplyValue s) in (n, k n)
   wrap2 s k =
     case split2 s of (s0, s1) -> wrap s0 (k s1)
   wrap3 s k =
     case split3 s of (s0, s1, s2) -> wrap s0 (k s1 s2)

   add_to_chunks chks chk_id chk = M.insert chk_id chk chks

   go s _env e@(ELit _ _) = wrap s $ \e_id ->
     M.singleton e_id $ Chunk
       { chunkExpr = e
       , chunkDepends = []
       , chunkHoles = []
       , rebuild = \ [] -> e
       , tcChunk =
           \jenv jstate -> 
               case stepJM jenv jstate $ tcExpr e of
                 (Left err, _) -> TcFail err
                 (Right ty, s') -> TcOk s' ty id
       }

   go s env (EApp l e1 e2) =
     wrap3 s $ \s1 s2 n ->
       let (h1, chks1) = go s1 env e1
           (h2, chks2) = go s2 env e2
           e = EApp l (hole h1 e1) (hole h2 e2)
       in add_to_chunks (chks1 `M.union` chks2) n $ Chunk
            { chunkExpr = e
            , chunkDepends = []
            , chunkHoles = [h1, h2]
            , rebuild = \ [e1', e2'] -> EApp l e1' e2'
            , tcChunk =
                \jenv jstate ->
                    case stepJM jenv jstate $ tcExpr e of
                      (Left err, _) -> TcFail err
                      (Right ty, s') -> TcOk s' ty id
            }

   go s env (ELam l p@(VarPat _ x) e1) =
     wrap2 s $ \s1 n ->
       let env' = extendEnv env x n
           (h1, chks1) = go s1 env' e1
           e = ELam l p (hole h1 e1)
       in add_to_chunks chks1 n $ Chunk
            { chunkExpr = e
            , chunkDepends = []
            , chunkHoles = [h1]
            , rebuild = \ [e1'] -> ELam l p e1'
            , tcChunk =
                \jenv jstate ->
                    -- See Note [Extracting Binder Types] below.
                    case stepJM jenv jstate $ do
                           fun_ty <- tcExpr e
                           existsId x $ \x_ty -> do
                           existsTy "r" $ \r_ty -> do
                           unify l (x_ty .->. r_ty) fun_ty
                           return (fun_ty, x_ty)
                    of
                      (Left err, _) -> TcFail err
                      (Right (ty, x_ty), s') ->
                          TcOk s' ty (\en -> extendLocalEnv' en x x_ty)
            }

   go s env e@(EVar _ x) =
     let deps = maybe [] (\n -> [n]) (lookupEnv env x) in
     wrap s $ \n ->
       M.singleton n $ Chunk
         { chunkExpr = e
         , chunkDepends = deps
         , chunkHoles = []
         , rebuild = \ [] -> e
         , tcChunk =
             \jenv jstate ->
                case stepJM jenv jstate $ tcExpr e of
                  (Left err, _) -> TcFail err
                  (Right ty, s') -> TcOk s' ty id
         }

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

-- -------------------------------------------------------------------
-- * Slicing

data SlicerState = SlicerState
  { chunkTypes :: M.Map ChunkId Type
  , chunkEnvs  :: M.Map ChunkId (JEnv -> JEnv)
  , tcState :: !JState
  }

instance Pretty SlicerState where
  ppr s = char '<' <> 
          (text "chunk-tys:" <+> ppr (chunkTypes s) $+$
           text "have-env:" <+> ppr (M.keysSet (chunkEnvs s)) $+$
           ppr (tcState s)) <> char '>'

holeTypes :: [ChunkId] -> JEnv -> SlicerState -> (SlicerState, [(ChunkId, Type)])
holeTypes hs env0 st0 = go hs (chunkTypes st0) (tcState st0) []
  where
    go [] !m !st !acc = (st0 { chunkTypes = m, tcState = st }, acc)
    go (cid:cids) !m !st !acc =
      case M.lookup cid m of
        Just ty -> go cids m st ((cid, ty):acc)
        Nothing ->
          case stepJM env0 st $ existsId cid $ return of
            (Right ty, st') ->
                go cids (M.insert cid ty m) st' ((cid, ty):acc)

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
minSlice :: Supply Unique -> GlobalEnv -> Expr -> Expr
minSlice supply gbl_env expr =
   mkSlice s2 (top_level, all_chunks) min_chunks
 where
   min_chunks = minimise state0 M.empty all_chunks

   top_level_env = setGlobalEnv emptyJEnv gbl_env
 
   state0 = SlicerState { chunkTypes = M.empty
                        , chunkEnvs = M.empty
                        , tcState = emptyState }
   (s1, s2) = split2 supply
   
   (top_level, all_chunks) = chop s1 expr

   minimise min_state min_approx not_tried =
     case solve_until_failure min_state min_approx not_tried of
       Right _ -> M.empty
       Left (last_tried_id, last_tried, _) ->
         -- TODO: need to add multiple things add once
         trace ("adding: " ++ pretty last_tried) $
         case solve_one min_state last_tried_id last_tried (chunkDepends last_tried) of
           Left _ -> M.insert last_tried_id last_tried min_approx
           Right min_state' ->
             minimise min_state' (M.insert last_tried_id last_tried min_approx)
                      (M.delete last_tried_id not_tried)

   --solve_until_failure s _ not_tried | trace (pretty (not_tried, s)) False = __
   solve_until_failure s min_approx not_tried =
     case M.minViewWithKey not_tried of
       Nothing -> Right s
       Just ((chk_id, chk), not_tried') ->
         -- Enforce dependency order:  If one of the dependencies of
         -- chk is not yet in `min_approx` try that first.
         let deps = chunkDepends chk
             (next_chk_id, next_chk) =
               case filter (`M.notMember` min_approx) deps of
                 [] -> (chk_id, chk)
                 (c:_) -> (c, all_chunks M.! c)
         in
           case solve_one s next_chk_id next_chk deps of
             Left ss' -> Left (next_chk_id, next_chk, ss')
             Right ss' -> solve_until_failure ss' min_approx not_tried'

   -- Construct environment based on the dependencies and whole variables.
   -- PreCond: all deps are in `min_approx`
   build_jenv ss jenv (dep:deps) holes =
     let mod_env = chunkEnvs ss M.! dep
         !jenv' = mod_env jenv
     in build_jenv ss jenv' deps holes
   build_jenv ss jenv [] holes =
     let (ss', hole_tys) = holeTypes holes jenv ss in
     (ss', jenv, hole_tys)
     

   solve_one ss chk_id chk deps =
     let (ss', jenv, hole_tys) =
             build_jenv ss top_level_env deps (chunkHoles chk)
         (Right jenv', tc_st) =
             stepJM jenv (tcState ss') $ do
               extendLocalEnvN hole_tys $ ask
     in
       trace ("tcChunk: " ++ pretty (colour1 (ppr chk_id) <+> ppr chk $+$ ppr jenv')) $
       case tcChunk chk jenv' tc_st of
         TcFail _err ->
           Left (ss{ tcState = tc_st })
         TcOk tc_st' ty mod_env ->
           case M.lookup chk_id (chunkTypes ss') of
             Nothing ->
               Right $
                 ss' { tcState = tc_st'
                     , chunkTypes = M.insert chk_id ty (chunkTypes ss')
                     , chunkEnvs = M.insert chk_id mod_env (chunkEnvs ss')
                     }
             Just hole_ty ->
               -- could be the case because this chunk occurred as a
               -- hole in another chunk
               case stepJM jenv' tc_st' $ unify noSrcSpan hole_ty ty of
                 (Left _, _) ->
                   Left (ss{ tcState = tc_st })
                 (Right _, tc_st'') ->
                   Right $
                     ss' { tcState = tc_st''
                         , chunkEnvs = M.insert chk_id mod_env (chunkEnvs ss')
                         }

mkSlice :: Supply Unique -> (ChunkId, Chunks) -> Chunks -> Expr
mkSlice supply (top_level, all_chunks) keep = go_ top_level
 where
   go_ nid = go (EVar noSrcSpan nid)
   go e@(EVar _ n)
--     | trace (pretty n) False = undefined
     | n `M.member` all_chunks =
        let chunk = all_chunks M.! n in
        if n `M.member` keep then
          rebuild chunk (map go_ (chunkHoles chunk))
        else merge (map go_ (chunkHoles chunk))
     | otherwise = e

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

   merge es0 = dots (merge' es0)
     where
       --merge' es | trace (pretty es) False = undefined
       merge' [] = []
       merge' (e:es) =
         case viewDots e of
           Nothing -> e : merge' es
           Just ds -> merge' ds ++ merge' es

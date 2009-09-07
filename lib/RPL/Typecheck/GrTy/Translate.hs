{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module RPL.Typecheck.GrTy.Translate where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Constraint
import RPL.Typecheck.GrTy.Syntactic
import qualified RPL.Type as Typ
import qualified RPL.BuiltIn as Typ
import qualified RPL.Syntax as Syn
import qualified RPL.Names as Syn
import RPL.Utils.Unique
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
import RPL.Utils.Monads
import RPL.Utils.Misc

import Data.Supply
import Control.Applicative
import qualified Data.Map as M
import Control.Monad ( when, foldM, forM_ )
import Data.Maybe ( isJust )
import Data.List ( intercalate, find )
import Graphics.Ubigraph

import System.Cmd
import System.FilePath ( (<.>) )
import System.Directory ( getTemporaryDirectory )
import System.IO

data GTMState = GTMState 
  { nextId :: Supply NodeId
  , st_edges :: [ConstrEdge]
  , st_exists :: [Node]
  , st_roots :: [Node] }
              
newtype GTM a = GTM (StrictStateErrorT GTMState String IO a)
  deriving (MonadIO, Applicative, Functor, Monad, MonadState GTMState,
            MonadError String)

instance MonadGen NodeId GTM where
  getSupply = gets nextId
  setSupply s' = modify $ \st -> st{ nextId = s' }

runGTM :: GTM a -> IO (Either String a)
runGTM (GTM m) = do
  nids <- newNumSupply
  fmap fst <$> runStrictStateErrorT m (GTMState nids [] [] [])

------------------------------------------------------------------------

-- TODO: what does this do?
copyConstraints :: ConstraintStore -> (Node -> Node) -> GTM ConstraintStore
copyConstraints cstore dest = do
   cs' <- mapM copy (cstore_constraints cstore)
   return $ cstore { cstore_constraints = cs' }
  where
    copy e@ConstrEdge{ cedge_from = n1, cedge_to = n2 } =
      ifM ((||) <$> copied n1 <*> copied n2)
        (do let n1' = dest n1
            whenM ((&&) <$> nodesEqual n1 n1' <*> isForall n1') $ do
              incrForallCount n1'
            return $ e { cedge_from = n1', cedge_to = dest n2 })
        (return e)

    copied n = not <$> nodesEqual (dest n) n

type Env = [()]

exists_ :: Node -> GTM ()
exists_ n = modify (\st -> st{ st_exists = n : st_exists st })

addConstraint :: ConstrEdge -> GTM ()
addConstraint e = modify (\st -> st{ st_edges = e : st_edges st })

inst_elim_mono :: ConstrEdge -> GTM ConstrEdge
inst_elim_mono e@ConstrEdge{ cedge_type = Unify } = return e
inst_elim_mono e@ConstrEdge{ cedge_from = f, cedge_to = d } = do
  [n] <- nodeChildren f
  -- ifM (n `isBoundAt` f)
  ifM (nodesEqual f =<< binderNode n)
    (return e)
    (do decrForallCount f
        return (ConstrEdge { cedge_type = Unify
                           , cedge_origin = cedge_origin e
                           , cedge_from = n
                           , cedge_to = d }))


-- | Add a constraint based whose type is determined based on the nodes.
--
-- @constrain n1 n2 o@ adds a constraint from @n1@ to @n2@.  The type of
-- constraint is figured out automatically based on the sort of nodes.  That
-- is, if the source is a forall node, add an instance constraint, otherwise
-- add a unification constraint.
constrain :: Node -> Node -> ConstrOrigin -> GTM ()
constrain n1 n2 origin = do
  ifM (isForall n1)
    (do incrForallCount n1
        addConstraint (ConstrEdge { cedge_type = Inst
                                  , cedge_origin = origin
                                  , cedge_from = n1
                                  , cedge_to = n2 }))
    (whenM (not <$> nodesEqual n1 n2) $
       addConstraint (ConstrEdge { cedge_type = Unify
                                 , cedge_origin = origin
                                 , cedge_from = n1
                                 , cedge_to = n2 }))

translate :: ConstrType -> Env -> Syn.Expr -> GTM ConstraintStore
translate ct _env exp0 = do
    f <- create_real_forall M.empty Nothing exp0 (exprToOrig exp0)
    edges <- mapM inst_elim_mono =<< (reverse <$> gets st_edges)
    ex <- gets st_exists
    return (ConstraintStore { cstore_constraints = edges
                            , cstore_existentials = ex
                            , cstore_root = f })
  where
    --  b <- bot
    --  mb_f -|<|- (forall >--< b)
    --  n <- translate_ vars f' f' e
    --  n =<= b
    create_real_forall vars mb_f e role = do
      b <- newNode Bot []
      f' <- newForallNode role [b]
      f' `bindFlexiblyTo` mb_f
      when (isJust mb_f) $
        exists_ f'
      n <- translate_ vars f' f' e
      fuse n b Nothing
      return f'

    create_forall vars fbind f e role = do
      -- TODO: optimise degenerate cases
      b <- newNode Bot []
      f' <- newForallNode role [b]
      exists_ f'
      f' `bindFlexiblyTo` (Just f)
      let bndr = case ct of
                     MLF -> f'
                     ML -> fbind
      r <- translate_ vars bndr f' e
      fuse r b Nothing
      return f'
   
    -- f is the current forall for the shape of the constraint
    -- bindf is the forall to which to bind nodes
    translate_ vars fbind f e = do
      let new_bound_node nsort children = 
              do n <- newNode nsort children
                 n `bindFlexiblyTo` (Just fbind)
                 return n
      case e of
        Syn.EVar _ name ->
          case M.lookup name vars of
            Just node' -> do
              var_occ <- new_bound_node Bot []
              constrain node' var_occ ()
              return var_occ
            Nothing ->
              throwError $ "unbound variable: " ++ pretty name

        Syn.ELam _ (Syn.VarPat _ var) body -> do
          -- arg <- newVar
          -- res <- newVar
          -- arr <- newTy (arg .->. res)
          arg <- new_bound_node Bot []
          res <- new_bound_node Bot []
          arr <- new_bound_node (TyConNode Typ.funTyCon) [arg, res]
          let vars' = M.insert var arg vars
          f_body <- create_forall vars' fbind f body (exprToOrig body)
          constrain f_body res ()
          return arr

        Syn.EApp _ e1 e2 -> do
          arg <- new_bound_node Bot []
          res <- new_bound_node Bot []
          arr <- new_bound_node (TyConNode Typ.funTyCon) [arg, res]
          exists_ arr
          
          ffun <- create_forall vars fbind f e1 (exprToOrig e1)
          farg <- create_forall vars fbind f e2 (exprToOrig e2)

          constrain farg arg ()
          constrain ffun arr ()

          return res

        Syn.ELit _ l -> do
          let t = case l of
                    Syn.IntLit _ -> Typ.typeInt
                    Syn.CharLit _ -> Typ.typeChar
          new_bound_node (TyConNode t) []

        Syn.ELet _ (Syn.VarPat _ v) e1 e2 -> do
          f1 <- create_real_forall vars (Just f) e1
                  (exprToOrig e1)
          let vars' = M.insert v f1 vars
          f2 <- translate_ vars' fbind f e2
          -- add l_expr_roots f1 (loc v)
          return f2

        Syn.EAnn _ e2 ty -> do
          co <- mkCoercion ty
          f' <- newForallNode (exprToOrig e) [co]
          f' `bindFlexiblyTo` (Just f)
          co `bindFlexiblyTo` (Just f')

          arg <- new_bound_node Bot []
          res <- new_bound_node Bot []
          arr <- new_bound_node (TyConNode Typ.funTyCon) [arg, res]
          exists_ arr
          
          farg <- create_forall vars fbind f e2 (exprToOrig e2)

          constrain farg arg ()
          constrain f' arr ()

          return res

t1 :: IO ()
t1 = do 
  let x = Syn.Id (uniqueFromInt 2) "x"
  let y = Syn.Id (uniqueFromInt 3) "y"
  let u = noSrcSpan
  let expr = Syn.ELam u (Syn.VarPat u x) $ --(Syn.EVar u x)
             Syn.ELam u (Syn.VarPat u y) $ 
              Syn.EApp u (Syn.EVar u y) 
                 (Syn.EApp u (Syn.EVar u x) (Syn.ELit u (Syn.IntLit 1)))
  r <- runGTM $ do 
         cs <- translate MLF [] expr
         liftIO $ do 
           dumpConstraints cs
           dottyConstraints cs ""
           ubigraphConstraints cs
--          let cb msg n = do nid <- nodeId n; print (msg, nid)
--          dfs_interior nodeChildren (cb "frontier") (cb "pre") (cb "post")
--                       (cstore_root cs)
         let Just inst_edge = find ((Inst==) . cedge_type) (cstore_constraints cs)
         (cs',n1') <- expandForall cs MLF inst_edge
         liftIO $ do 
           dumpConstraints cs'
           dottyConstraints cs' ""
         return ()
      
  case r of
    Left s -> print s
    Right _ -> return ()
  return ()


exprToOrig :: Syn.Expr -> ForallOrigin
exprToOrig (Syn.ELam _ _ _) = FOText "\\"
exprToOrig (Syn.EApp _ _ _) = FOText "@"
exprToOrig (Syn.EVar _ v) = FOText (pretty v)
exprToOrig (Syn.ELit _ l) = FOText (pretty l)
exprToOrig (Syn.EAnn _ _ t) = FOText ("::" ++ pretty t)
exprToOrig (Syn.ELet _ (Syn.VarPat _ v) _ _) =
  FOText (pretty v ++ "=")

dumpConstraints :: ConstraintStore -> IO ()
dumpConstraints st = do
   r_id <- nodeId (cstore_root st)

--    nodes <- trans_close (cstore_root st : cstore_existentials st) M.empty
--    putStrLn . ("All: "++) . intercalate ", " =<< mapM ppNode (M.elems nodes)

   putStrLn . ("Root: " ++) =<< ppNode (cstore_root st)
   ns0 <- M.fromList <$> mapM (\n -> do i <- nodeId n; return (i, n))
                             (cstore_existentials st)
   putStrLn . ("Exist: "++) . intercalate ", " =<< mapM ppNode (M.elems ns0)
   let ns1 = M.insert r_id (cstore_root st) ns0
   ns2 <- foldM add_cnode ns1 (cstore_constraints st)
   ns3 <- trans_close (M.elems ns2) M.empty
   let ns = ns3 `M.difference` ns1
   putStrLn . ("Other: "++) . intercalate ", " =<< mapM ppNode (M.elems ns)
   putStrLn . ("Constrs: "++) . intercalate ", " =<< mapM ppEdge (cstore_constraints st)
 where
    ppNode n = do
      i <- nodeId n
      s <- nodeSort n
      cis <- mapM nodeId =<< nodeChildren n
      return (ppSort s ++ "_" ++ show i ++ " -> " ++ show cis)
    
    add_cnode ns edge = do
      n1 <- nodeId (cedge_from edge)
      n2 <- nodeId (cedge_to edge)
      return (M.insert n1 (cedge_from edge) $
              M.insert n2 (cedge_to edge) ns)

    ppEdge edge = do
      n1 <- nodeId (cedge_from edge)
      n2 <- nodeId (cedge_to edge)
      let knd = case cedge_type edge of
                  Unify -> " == "
                  Inst -> " => "
      return (show n1 ++ knd ++ show n2)
        
trans_close :: [Node] -> M.Map Int Node -> IO (M.Map Int Node)
trans_close [] res = return res
trans_close (r:rs) res = do
  r_id <- nodeId r
  if M.member r_id res
   then trans_close rs res
   else do
     r's <- nodeChildren r
     trans_close (r's ++ rs) (M.insert r_id r res)


ppSort :: NodeSort -> String
ppSort (TyConNode tc) = Syn.idString (Typ.tyConName tc)
ppSort (TypeNode _)  = "T"
ppSort Bot           = "v"
ppSort (Forall orig _)    = ppOrig orig

ppOrig (FOSpan loc) = pretty (ppSpanRegion loc)
ppOrig (FOText t) = t

dottyConstraints :: ConstraintStore -> String -> IO ()
dottyConstraints cs title = do
    nodes <- trans_close (cstore_root cs : cstore_existentials cs) M.empty
    nlines <- mapM ppNode (M.elems nodes)
    elines <- mapM ppEdge (cstore_constraints cs)
    let dotty_descr = header ++ unlines (nlines ++ elines) ++ footer
  
    let dotty_cmd = "dot"
    let open_png = "open"
    tmp_dir <- getTemporaryDirectory
    (path, h) <- openTempFile tmp_dir "dotdump"
    hPutStr h dotty_descr
    hFlush h
    hClose h
    let out = path <.> "png"
    rawSystem dotty_cmd ["-Tpng", "-o", out, path ]
    rawSystem open_png [out] 
    
    return () --dotty_descr
  where
    header = unlines ["digraph tygraph {"
                     ,"\tgraph[fontsize=14, fontcolor=black, color=black, label="++show title++"];"
                     ,"\tnode [label=\"\\N\", width=\"0.35\", shape=circle];"
                     ,"\tedge [fontsize=10];"]
    footer = "}\n"
    ppNode n = do
      i <- nodeId n
      s <- nodeSort n
      r <- isRoot n
      ch <- mapM nodeId =<< nodeChildren n
      bdr <- getBinder n
      bind_edge
        <- (case bdr of
              Root -> return []
              Bound b -> do
                b_id <- nodeId (bindBinder b)
                f <- isForall (bindBinder b)
                return $ 
                  ["\t" ++ show b_id ++ " -> " ++ show i
                        ++ " [dir=back" -- , constraint=" ++ (if f then "true" else "false") 
                        ++ ", style=" ++ 
                        (case bindLabel b of
                           Flex -> "dotted"
                           Rigid -> "dashed") ++ "];"])
      return $ unlines $
         [ "\t" ++ show i ++ " [label=" ++ show (show i ++ " " ++ ppSort s) ++ 
           (if r then ",shape=doublecircle" else "") ++
           (case s of
              Forall _ _ -> ",color=gray"
              _ -> "")
           ++ "];" ] ++ 
         [ "\t" ++ show i ++ " -> " ++ show c ++ " [label=" ++ show (show m) ++ "];" 
            | (c,m) <- zip ch [(1::Int)..] ]
         ++ bind_edge

    ppEdge e = do
      n1 <- nodeId (cedge_from e)
      n2 <- nodeId (cedge_to e)
      return $ "\t" ++ show n1 ++ " -> " ++ show n2 ++ " [constraint=false," ++ 
               (case cedge_type e of
                  Unify -> "arrowhead=none, color=green"
                  Inst -> "color=red")
               ++ "];" 

ubigraphConstraints :: ConstraintStore -> IO ()
ubigraphConstraints cstore = do
   clear defaultServer
   nodes <- trans_close (cstore_root cstore : cstore_existentials cstore) M.empty
   mapM_ (uncurry mkVertex) (M.toList nodes)
   mapM_ (uncurry ppNode) (M.toList nodes)
   mapM_ ppEdge (cstore_constraints cstore)
   return ()
  where
    mkVertex nid node = do
      newVertexWithId defaultServer nid
      nsort <- nodeSort node
      case nsort of
        TyConNode tc -> do
          setVertexAttribute defaultServer nid "color" "#8888ff"
          setVertexAttribute defaultServer nid "shape" "cube"
          setVertexAttribute defaultServer nid "label" (ppSort nsort)
        TypeNode _ -> 
          setVertexAttribute defaultServer nid "color" "#0000ff"
        Bot -> do
          setVertexAttribute defaultServer nid "color" "#ff0000"
          setVertexAttribute defaultServer nid "shape" "sphere"
        Forall _ _ -> do
          setVertexAttribute defaultServer nid "color" "#008800"
          setVertexAttribute defaultServer nid "shape" "cube"
          r <- isRoot node
          if r then setVertexAttribute defaultServer nid "size" "2.0" else return True
 
    ppNode nid node = do
      ch <- mapM nodeId =<< nodeChildren node
      forM_ ch $ \child_id -> do
        e <- newEdge defaultServer nid child_id
        setEdgeAttribute defaultServer e "color" "#ffffff"
        setEdgeAttribute defaultServer e "oriented" "true"
        return ()
      bdr <- getBinder node
      case bdr of
        Root -> return ()
        Bound b -> do
          b_id <- nodeId (bindBinder b)
          e <- newEdge defaultServer b_id nid
          setEdgeAttribute defaultServer e "color" "#008800"
          setEdgeAttribute defaultServer e "strength" "0.3"
          setEdgeAttribute defaultServer e "oriented" "true"
          return ()
                 
    ppEdge e = do
      n1 <- nodeId (cedge_from e)
      n2 <- nodeId (cedge_to e)
      ue <- newEdge defaultServer n1 n2
      setEdgeAttribute defaultServer ue "width" "3"
      setEdgeAttribute defaultServer ue "strength" "0.1"
      case cedge_type e of
        Unify -> setEdgeAttribute defaultServer ue "color" "#00ff00"
        Inst -> setEdgeAttribute defaultServer ue "color" "#ff0000"
      return ()

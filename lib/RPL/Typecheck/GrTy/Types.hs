{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module RPL.Typecheck.GrTy.Types where

import qualified RPL.Type as Typ
import qualified RPL.Syntax as Syn
import qualified RPL.Names as Syn
import RPL.Utils.Unique
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Monads
import RPL.Utils.Panic
import RPL.Utils.Pretty
import RPL.Utils.SrcLoc
import RPL.Utils.Misc

import Data.Supply
import Control.Applicative
import Data.IORef
import Data.Maybe ( isJust )
import Control.Monad ( when, foldM )
import Data.List ( intercalate )
import Control.Monad.Fix
import qualified Data.Map as M

import System.IO.Unsafe ( unsafePerformIO )

------------------------------------------------------------------------

data GTMState = GTMState 
  { nextId :: Supply NodeId
  , st_edges :: [ConstrEdge]
  , st_exists :: [Node]
  , st_roots :: [Node] }
              
newtype GTM a = GTM (StrictStateErrorT GTMState String IO a)
  deriving (MonadIO, Applicative, Functor, Monad, MonadState GTMState,
            MonadError String)

runGTM :: GTM a -> IO (Either String a)
runGTM (GTM m) = do
  nids <- newNumSupply
  fmap fst <$> runStrictStateErrorT m (GTMState nids [] [] [])

-- * Terms

newNodeId :: GTM NodeId
newNodeId = do
  s <- gets nextId
  let (s', s'') = split2 s
  modify $ \st -> st{ nextId = s'' }
  return (supplyValue s')

newtype GTRef a = GTRef { unGTRef :: IORef a } deriving (Eq)
instance Show a => Show (GTRef a) where
  show (GTRef r) = "<ref>" --show (unsafePerformIO $ readIORef r)

newRef :: MonadIO m => a -> m (GTRef a)
newRef x = liftIO $ GTRef <$> newIORef x

readRef :: MonadIO m => GTRef a -> m a
readRef (GTRef r) = liftIO $ readIORef r

writeRef :: MonadIO m => GTRef a -> a -> m ()
writeRef (GTRef r) x' = liftIO $ writeIORef r x'

modifyRef :: MonadIO m => GTRef a -> (a -> a) -> m ()
modifyRef (GTRef r) f = liftIO $ modifyIORef r f

data Node = Node
  { node_info :: UF.Point NodeInfo
  , oldStruct :: UF.Point OldStruct
  } deriving (Eq)

instance Show Node where
  show (Node i _) = unsafePerformIO (show <$> UF.descriptor i)

newtype NodeId = NodeId { unNodeId :: Int } deriving (Eq, Ord, Show, Num)

data Permissions = FlexPerm | RigidPerm | LockedPerm
  deriving (Eq, Ord, Show)

data BindingLabel = Flex | Rigid
  deriving (Eq, Ord, Show)

-- | A reference counter for @forall@ nodes.
newtype ForallUse = ForallUse (GTRef Int) deriving (Eq)

instance Show ForallUse where show _ = "ForallUse"

-- | The sort (or type) of a node.  I.e., G-node, bottom-node or
-- constructor.
data NodeSort
  = TyConNode Typ.TyCon
  | TypeNode Typ.Type
  | Bot
  | Forall ForallUse
  deriving (Eq, Show)

data NodeInfo = NodeInfo
  { node_id       :: {-# UNPACK #-} !NodeId
  , nodeSort      :: NodeSort
  , node_children  :: [Node] -- TODO: invariant? length == arity?
  , nodeBound     :: GTRef (Bound Node)
  , nodeCanon     :: Node -- ??
  , nodeUnifyInfo :: UnifyInfo
  } deriving (Eq, Show)

data Bound a = Root | Bound (BoundInfo a) deriving (Eq, Show)

data BoundInfo a = BoundInfo
  { bindLabel       :: {-# UNPACK #-} !BindingLabel
  , bindBinder          :: a
  , bindPermissions :: {-# UNPACK #-} !Permissions
  , bindHeight      :: {-# UNPACK #-} !Int
  } deriving (Eq, Show)

data UnifyInfo = UnifyInfo
  { unifyTag :: () -- TODO:
  } deriving (Eq, Show)

data OldStruct = OldStruct deriving (Eq, Show)

-- | Create a new node of the given sort and children.
newNode :: NodeSort -> [Node] -> GTM Node
newNode nsort0 children = do
  nsort <- case nsort0 of
             Forall (ForallUse r) -> do
               -- Don't share the reference from the argument.
               count <- readRef r
               r' <- newRef count
               return $ Forall (ForallUse r')
             _ -> return nsort0

  nid <- newNodeId
  let unify_info = UnifyInfo { unifyTag = () }
  let old_struct = OldStruct
  node
      <- liftIO $ mfix $ \ n -> do
           bound_ref <- newRef Root
           let node_info' = 
                   NodeInfo { node_id = nid
                            , nodeSort = nsort
                            , node_children = children
                            , nodeBound = bound_ref
                            , nodeCanon = n
                            , nodeUnifyInfo = unify_info
                            }
           ni <- UF.fresh node_info'
           nos <- UF.fresh old_struct
           let node = Node ni nos
           return node
  return node

-- | Get the current node info of the node.
nodeInfo :: MonadIO m => Node -> m NodeInfo
nodeInfo (Node ni _) = liftIO $ UF.descriptor ni

-- | Return the id of the node as an integer.
nodeId :: (Applicative m, MonadIO m) => Node -> m Int
nodeId node = unNodeId . node_id <$> nodeInfo node

nodesEqual :: Node -> Node -> GTM Bool
nodesEqual n1 n2 = (==) <$> nodeId n1 <*> nodeId n2

nodeArity :: Node -> GTM Int
nodeArity node = do
  nsort <- nodeSort <$> nodeInfo node
  return $ case nsort of
             Bot -> 0
             Forall _ -> 1
             TypeNode _ -> 0
             TyConNode tc -> Typ.tyConArity tc

-- | Set the binder of the given node.
setBinder :: Node -> BoundInfo Node -> GTM ()
setBinder node binfo = do
  ni <- nodeInfo node
  writeRef (nodeBound ni) (Bound binfo)

nodeBinder :: Node -> GTM Node
nodeBinder node = do
  b <- get_binder node
  case b of
    Root -> error "nodeBinder of root"
    Bound b' -> return (bindBinder b')

get_binder :: (Applicative m, MonadIO m) => Node -> m (Bound Node)
get_binder node = readRef =<< nodeBound <$> nodeInfo node

set_binder :: Node -> Bound Node -> GTM ()
set_binder node b' = do
  r <- nodeBound <$> nodeInfo node
  writeRef r b'

nodeChildren :: (Applicative m, MonadIO m) => Node -> m [Node]
nodeChildren node = node_children <$> nodeInfo node

-- | Returns @True@ iff node is a root.
isRoot :: (Applicative m, MonadIO m) => Node -> m Bool
isRoot node = do
  ni <- nodeInfo node
  b <- readRef (nodeBound ni)
  case b of
    Root -> return True
    _ -> return False


fuse :: Node -> Node -> GTM ()
fuse keep@(Node ni1 os1) (Node ni2 os2) = do
  bound <- get_binder keep
  liftIO $ UF.union ni2 ni1
  set_binder keep bound
  liftIO $ UF.union os2 os1

-- | Create a new forall node sort.
newForallSort :: GTM NodeSort
newForallSort = Forall . ForallUse <$> liftIO (newRef 0)

newForallNode :: [Node] -> GTM Node
newForallNode children = do
  fa <- newForallSort
  newNode fa children

isForall :: Node -> GTM Bool
isForall node = do
  nsort <- nodeSort <$> nodeInfo node
  case nsort of
    Forall _ -> return True
    _ -> return False

-- | Return number of references to this forall, i.e., the number of
-- variables bound at this forall node.
forallCount :: Node -> GTM Int
forallCount node = readRef =<< forall_count_ref node

-- | Return the reference of the forall use counter.
forall_count_ref :: Node -> GTM (GTRef Int)
forall_count_ref node = do
  nsort <- nodeSort <$> nodeInfo node
  case nsort of
    Forall (ForallUse r) -> return r
    _ -> panic (text "forall_count_ref: Node not a forall")

-- | Increase the forall use counter by 1.
incrForallCount :: Node -> GTM ()
incrForallCount node = flip modifyRef succ =<< forall_count_ref node

-- | Decrease the forall use counter by 1.
decrForallCount :: Node -> GTM ()
decrForallCount node = flip modifyRef pred =<< forall_count_ref node

bindingHeight :: Node -> GTM Int
bindingHeight node = do
  bndr <- get_binder node
  case bndr of
    Root -> return 0
    Bound binfo -> return (bindHeight binfo)

bindFlexiblyTo :: Node -> Maybe Node -> GTM ()
bindFlexiblyTo node mb_binder = do
  bind_ref <- nodeBound <$> nodeInfo node
  writeRef bind_ref =<<
    case mb_binder of
      Nothing -> return Root
      Just n' -> do
        height' <- bindingHeight n'
        return $ Bound (BoundInfo { bindLabel = Flex
                                  , bindBinder = n'
                                  , bindPermissions = FlexPerm
                                  , bindHeight = height' + 1
                                  })

------------------------------------------------------------------------

-- * Constraints

-- | The origin and role of a constraint.
--
-- E.g., \"ensure that both if-branches have the same type\".
--
-- TODO: implement this
type ConstrOrigin = ()

-- | The type of a constaint.  Currently only unification and instantiation
-- constraints are supported.  Eventually we'd like to have instance
-- constraints as well.
data ConstrEdgeType = Unify | Inst deriving (Eq, Show)

-- | A constraint.  Constraints a binary and relate two types; hence they
-- can be represented by a single (possibly directed) edge in the graphical
-- type.
data ConstrEdge = ConstrEdge
  { cedge_type   :: ConstrEdgeType
  , cedge_origin :: ConstrOrigin
    -- ^ The source code origin of the frame and its role.  
  , cedge_from   :: Node
  , cedge_to     :: Node
  } deriving (Eq, Show)

-- | All the constraints in a type checking unit.
data ConstraintStore = ConstraintStore
  { cstore_root :: Node
  , cstore_constraints :: [ConstrEdge]
  , cstore_existentials :: [Node]
  } deriving (Eq, Show)


------------------------------------------------------------------------
-- * Constraint Generation

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

data ConstrType = MLF | ML

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
  ifM (nodesEqual f =<< nodeBinder n)
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
translate ct env exp0 = do
    f <- create_real_forall M.empty Nothing exp0
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
    create_real_forall vars mb_f e = do
      b <- newNode Bot []
      f' <- newForallNode [b]
      f' `bindFlexiblyTo` mb_f
      when (isJust mb_f) $
        exists_ f'
      n <- translate_ vars f' f' e
      fuse n b
      return f'

    create_forall vars fbind f e = do
      -- TODO: optimise degenerate cases
      b <- newNode Bot []
      f' <- newForallNode [b]
      exists_ f'
      f' `bindFlexiblyTo` (Just f)
      let bndr = case ct of
                     MLF -> f'
                     ML -> fbind
      r <- translate_ vars bndr f' e
      fuse r b
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
              throwError $ "unbound variable:" ++ pretty name

        Syn.ELam _ (Syn.VarPat _ var) body -> do
          -- arg <- newVar
          -- res <- newVar
          -- arr <- newTy (arg .->. res)
          arg <- new_bound_node Bot []
          res <- new_bound_node Bot []
          arr <- new_bound_node (TyConNode Typ.funTyCon) [arg, res]
          let vars' = M.insert var arg vars
          f_body <- create_forall vars' fbind f body
          constrain f_body res ()
          return arr

t1 :: IO ()
t1 = do 
  let x = Syn.Id (uniqueFromInt 2) "x"
  let u = noSrcSpan
  let expr = Syn.ELam u (Syn.VarPat u x) (Syn.EVar u x)
  r <- runGTM $ translate MLF [] expr
  case r of
    Left s -> print s
    Right cs -> do
           dumpConstraints cs
           writeFile "gtdump.dot" =<< dottyConstraints cs
  return ()

dumpConstraints :: ConstraintStore -> IO ()
dumpConstraints st = do
   r_id <- nodeId (cstore_root st)
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
      s <- nodeSort <$> nodeInfo n
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
ppSort (Forall _)    = "G"


dottyConstraints :: ConstraintStore -> IO String
dottyConstraints cs = do
    nodes <- trans_close (cstore_root cs : cstore_existentials cs) M.empty
    nlines <- mapM ppNode (M.elems nodes)
    elines <- mapM ppEdge (cstore_constraints cs)
    return $ header ++ unlines (nlines ++ elines) ++ footer
  where
    header = unlines ["digraph tygraph {"
                     ,"\tgraph[fontsize=14, fontcolor=black, color=black];"
                     ,"\tnode [label=\"\\N\", width=\"0.35\", shape=circle];"
                     ,"\tedge [fontsize=10];"]
    footer = "}\n"
    ppNode n = do
      i <- nodeId n
      s <- nodeSort <$> nodeInfo n
      r <- isRoot n
      cs <- mapM nodeId =<< nodeChildren n
      bdr <- get_binder n
      bind_edge
        <- (case bdr of
              Root -> return []
              Bound b -> do
                b_id <- nodeId (bindBinder b)
                return $ 
                  ["\t" ++ show i ++ " -> " ++ show b_id
                        ++ " [constraint=false, style=" ++ 
                        (case bindLabel b of
                           Flex -> "dotted"
                           Rigid -> "dashed") ++ "];"])
      return $ unlines $
         [ "\t" ++ show i ++ " [label=" ++ show (ppSort s) ++ 
           (if r then ",shape=doublecircle" else "") 
           ++ "];" ] ++ 
         [ "\t" ++ show i ++ " -> " ++ show c ++ ";" | c <- cs ]
         ++ bind_edge

    ppEdge e = do
      n1 <- nodeId (cedge_from e)
      n2 <- nodeId (cedge_to e)
      return $ "\t" ++ show n1 ++ " -> " ++ show n2 ++ " [constraint=true," ++ 
               (case cedge_type e of
                  Unify -> "arrowhead=none, color=green"
                  Inst -> "color=red")
               ++ "];" 

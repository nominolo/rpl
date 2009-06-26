{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module RPL.Typecheck.GrTy.Types where

import qualified RPL.Type as Syn
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Monads
import RPL.Utils.Panic
import RPL.Utils.Pretty

import Data.Supply
import Control.Applicative
import Data.IORef
import Control.Monad.Fix

------------------------------------------------------------------------

type GTMState = Supply NodeId

newtype GTM a = GTM (StrictStateErrorT GTMState String IO a)
  deriving (MonadIO, Applicative, Functor, Monad, MonadState GTMState)

runGTM :: GTM a -> IO (Either String a)
runGTM (GTM m) = do
  nids <- newNumSupply
  fmap fst <$> runStrictStateErrorT m nids

-- * Terms

newNodeId :: GTM NodeId
newNodeId = do
  s <- get
  let (s', s'') = split2 s
  put s''
  return (supplyValue s')

type GTRef a = IORef a

newRef :: MonadIO m => a -> m (GTRef a)
newRef x = liftIO $ newIORef x

readRef :: MonadIO m => GTRef a -> m a
readRef r = liftIO $ readIORef r

writeRef :: MonadIO m => GTRef a -> a -> m ()
writeRef r x' = liftIO $ writeIORef r x'

modifyRef :: MonadIO m => GTRef a -> (a -> a) -> m ()
modifyRef r f = liftIO $ modifyIORef r f

data Node = Node
  { node_info :: UF.Point NodeInfo
  , oldStruct :: UF.Point OldStruct
  }

newtype NodeId = NodeId { unNodeId :: Int } deriving (Eq, Ord, Show, Num)

data Permissions = FlexPerm | RigidPerm | LockedPerm
  deriving (Eq, Ord, Show)

data BindingLabel = Flex | Rigid
  deriving (Eq, Ord, Show)

-- | A reference counter for @forall@ nodes.
newtype ForallUse = ForallUse (GTRef Int)

-- | The sort (or type) of a node.  I.e., G-node, bottom-node or
-- constructor.
data NodeSort
  = TyConNode Syn.TyCon
  | TypeNode Syn.Type
  | Bot
  | Forall ForallUse

data NodeInfo = NodeInfo
  { node_id       :: {-# UNPACK #-} !NodeId
  , nodeSort      :: NodeSort
  , nodeChildren  :: [Node] -- TODO: invariant? length == arity?
  , nodeBound     :: GTRef (Bound Node)
  , nodeCanon     :: Node -- ??
  , nodeUnifyInfo :: UnifyInfo
  }

data Bound a = Root | Bound (BoundInfo a) deriving Eq

data BoundInfo a = BoundInfo
  { bindLabel       :: {-# UNPACK #-} !BindingLabel
  , binder          :: a
  , bindPermissions :: {-# UNPACK #-} !Permissions
  , bindHeight      :: {-# UNPACK #-} !Int
  } deriving Eq

data UnifyInfo = UnifyInfo
  { unifyTag :: () -- TODO:
  }

data OldStruct = OldStruct

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
                            , nodeChildren = children
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
nodeInfo :: Node -> GTM NodeInfo
nodeInfo (Node ni _) = liftIO $ UF.descriptor ni

-- | Return the id of the node as an integer.
nodeId :: Node -> GTM Int
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
             TyConNode tc -> Syn.tyConArity tc

-- | Set the binder of the given node.
setBinder :: Node -> BoundInfo Node -> GTM ()
setBinder node binfo = do
  ni <- nodeInfo node
  liftIO $ writeIORef (nodeBound ni) (Bound binfo)

get_binder :: Node -> GTM (Bound Node)
get_binder node = readRef =<< nodeBound <$> nodeInfo node

-- | Returns @True@ iff node is a root.
isRoot :: Node -> GTM Bool
isRoot node = do
  ni <- nodeInfo node
  b <- readRef (nodeBound ni)
  case b of
    Root -> return True
    _ -> return False

-- | Create a new forall node sort.
newForallSort :: GTM NodeSort
newForallSort = Forall . ForallUse <$> liftIO (newRef 0)

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
                                  , binder = n'
                                  , bindPermissions = FlexPerm
                                  , bindHeight = height' + 1
                                  })

------------------------------------------------------------------------

-- * Constraints

type ConstrOrigin = () -- TODO: supposed to point to the source

data ConstrEdgeType = Unify | Inst

data ConstrEdge = ConstrEdge
  { cedge_type   :: ConstrEdgeType
  , cedge_origin :: ConstrOrigin
  , cedge_from   :: Node
  , cedge_to     :: Node
  }

data Constraints = Constraints
  { constr_root :: Node
  , constraints :: [ConstrEdge]
  , constr_existentials :: [Node]
  }


------------------------------------------------------------------------
-- * Constraint Generation



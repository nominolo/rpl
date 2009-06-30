{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module RPL.Typecheck.GrTy.Types where

import qualified RPL.Type as Typ
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Monads
import RPL.Utils.Panic
import RPL.Utils.Pretty

import Control.Applicative
import Data.IORef
import Control.Monad.Fix

import System.IO.Unsafe ( unsafePerformIO )

------------------------------------------------------------------------

-- * References

newtype GTRef a = GTRef { unGTRef :: IORef a } deriving (Eq)
instance Show a => Show (GTRef a) where
  show (GTRef _) = "<ref>" --show (unsafePerformIO $ readIORef r)

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

-- * Terms

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

newNodeId :: MonadGen NodeId m => m NodeId
newNodeId = fresh

-- | Create a new node of the given sort and children.
newNode :: (MonadIO m, MonadGen NodeId m) => 
           NodeSort -> [Node] -> m Node
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

nodesEqual :: (Applicative m, MonadIO m) => Node -> Node -> m Bool
nodesEqual n1 n2 = (==) <$> nodeId n1 <*> nodeId n2

nodeArity :: (Applicative m, MonadIO m) => Node -> m Int
nodeArity node = do
  nsort <- nodeSort <$> nodeInfo node
  return $ case nsort of
             Bot -> 0
             Forall _ -> 1
             TypeNode _ -> 0
             TyConNode tc -> Typ.tyConArity tc

-- | Set the binder of the given node.
setBinder :: (Applicative m, MonadIO m) => Node -> BoundInfo Node -> m ()
setBinder node binfo = do
  ni <- nodeInfo node
  writeRef (nodeBound ni) (Bound binfo)

nodeBinder :: (Applicative m, MonadIO m) => Node -> m Node
nodeBinder node = do
  b <- get_binder node
  case b of
    Root -> error "nodeBinder of root"
    Bound b' -> return (bindBinder b')

get_binder :: (Applicative m, MonadIO m) => Node -> m (Bound Node)
get_binder node = readRef =<< nodeBound <$> nodeInfo node

set_binder :: (Applicative m, MonadIO m) => Node -> Bound Node -> m ()
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


fuse :: (Applicative m, MonadIO m) => Node -> Node -> m ()
fuse keep@(Node ni1 os1) (Node ni2 os2) = do
  bound <- get_binder keep
  liftIO $ UF.union ni2 ni1
  set_binder keep bound
  liftIO $ UF.union os2 os1

-- | Create a new forall node sort.
newForallSort :: (Applicative m, MonadIO m) => m NodeSort
newForallSort = Forall . ForallUse <$> liftIO (newRef 0)

newForallNode :: (Applicative m, MonadIO m, MonadGen NodeId m) => 
                 [Node] -> m Node
newForallNode children = do
  fa <- newForallSort
  newNode fa children

isForall :: (Applicative m, MonadIO m) => Node -> m Bool
isForall node = do
  nsort <- nodeSort <$> nodeInfo node
  case nsort of
    Forall _ -> return True
    _ -> return False

-- | Return number of references to this forall, i.e., the number of
-- variables bound at this forall node.
forallCount :: (Applicative m, MonadIO m) => Node -> m Int
forallCount node = readRef =<< forall_count_ref node

-- | Return the reference of the forall use counter.
forall_count_ref :: (Applicative m, MonadIO m) => Node -> m (GTRef Int)
forall_count_ref node = do
  nsort <- nodeSort <$> nodeInfo node
  case nsort of
    Forall (ForallUse r) -> return r
    _ -> panic (text "forall_count_ref: Node not a forall")

-- | Increase the forall use counter by 1.
incrForallCount :: (Applicative m, MonadIO m) => Node -> m ()
incrForallCount node = flip modifyRef succ =<< forall_count_ref node

-- | Decrease the forall use counter by 1.
decrForallCount :: (Applicative m, MonadIO m) => Node -> m ()
decrForallCount node = flip modifyRef pred =<< forall_count_ref node

bindingHeight :: (Applicative m, MonadIO m) => Node -> m Int
bindingHeight node = do
  bndr <- get_binder node
  case bndr of
    Root -> return 0
    Bound binfo -> return (bindHeight binfo)

bindFlexiblyTo :: (Applicative m, MonadIO m) => Node -> Maybe Node -> m ()
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

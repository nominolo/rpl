{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module RPL.Typecheck.GrTy.Types 
  ( Node(node_info), NodeId, Permissions(..), BindingLabel(..), ForallUse, NodeSort(..),
    Bound(..), BoundInfo(..), 
    NodeInfo(node_id, node_sort, node_children, nodeUnifyInfo, nodeBound),
    UnifyInfo(..), HistTree(..),
    newNode, nodeId, nodeSort, nodeArity, nodeChildren,
    isRoot, setBinder, getBinder, binderNode, 
    fuse, nodesEqual, 
    newForallNode, isForall, forallCount, incrForallCount, decrForallCount,
    bindingHeight,
    bindFlexiblyTo, bindTo,
    GTRef, newRef, readRef, writeRef, modifyRef,
    permissions_syst
  )
where

import qualified RPL.Type as Typ
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Monads
import RPL.Utils.Panic
import RPL.Utils.Pretty

import Control.Applicative
import Data.IORef
import Control.Monad.Fix
import Data.Maybe ( fromMaybe )
import Data.Unique

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
modifyRef (GTRef r) f = liftIO $ do x <- readIORef r
                                    writeIORef r $! f x

data Node = Node
  { node_info :: UF.Point NodeInfo
  , old_struct :: UF.Point OldStruct
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
  , node_sort      :: NodeSort
  , node_children  :: [Node] -- TODO: invariant? length == arity?
  , nodeBound     :: GTRef (Bound Node)
  , nodeCanon     :: Node -- ??
  , nodeUnifyInfo :: GTRef UnifyInfo
  } deriving (Eq, Show)

data Bound a = Root | Bound (BoundInfo a) deriving (Eq, Show)

data BoundInfo a = BoundInfo
  { bindLabel       :: {-# UNPACK #-} !BindingLabel
  , bindBinder      :: a
  , bindPermissions :: {-# UNPACK #-} !Permissions
  , bindHeight      :: {-# UNPACK #-} !Int
  } deriving (Eq, Show)

data UnifyInfo = UnifyInfo
  { unifyTag :: !Unique
  , unifiedNodes :: HistTree
  , unifyBotNonBot :: {-# UNPACK #-} !Bool
  , unifyMergeHappened :: {-# UNPACK #-} !Bool
  } deriving (Eq, Show)

data HistTree 
  = Empty 
  | Leaf {-# UNPACK #-} !NodeId
         (Bound Node)
  | Branch HistTree HistTree
  deriving (Eq, Show)

instance Show Unique where show u = "u<" ++ show (hashUnique u) ++ ">"

data OldStruct = OldStruct deriving (Eq, Show)

dummyTag :: Unique
dummyTag = unsafePerformIO $ newUnique

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
  unify_info <- newRef $ UnifyInfo 
                  { unifyTag = dummyTag
                  , unifiedNodes = Empty
                  , unifyBotNonBot = False
                  , unifyMergeHappened = False }
  let old_struct_ = OldStruct
  node
      <- liftIO $ mfix $ \ n -> do
           bound_ref <- newRef Root
           let node_info' = 
                   NodeInfo { node_id = nid
                            , node_sort = nsort
                            , node_children = children
                            , nodeBound = bound_ref
                            , nodeCanon = n
                            , nodeUnifyInfo = unify_info
                            }
           ni <- UF.fresh node_info'
           nos <- UF.fresh old_struct_
           let node = Node { node_info = ni, old_struct = nos }
           return node
  return node

-- | Get the current node info of the node.
nodeInfo :: MonadIO m => Node -> m NodeInfo
nodeInfo (Node ni _) = liftIO $ UF.descriptor ni

-- | Return the id of the node as an integer.
nodeId :: (Applicative m, MonadIO m) => Node -> m Int
nodeId node = unNodeId . node_id <$> nodeInfo node

nodeSort :: (Applicative m, MonadIO m) => Node -> m NodeSort
nodeSort node = node_sort <$> nodeInfo node

nodesEqual :: (Applicative m, MonadIO m) => Node -> Node -> m Bool
nodesEqual n1 n2 = (==) <$> nodeId n1 <*> nodeId n2

nodeArity :: (Applicative m, MonadIO m) => Node -> m Int
nodeArity node = do
  nsort <- nodeSort node
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

getBinder :: (Applicative m, MonadIO m) => Node -> m (Bound Node)
getBinder node = get_binder node

-- | Returns the node where the given node is bound at.
--
-- NOTE: The input node must not be a the root note.
binderNode :: (Applicative m, MonadIO m) => Node -> m Node
binderNode node = do
  b <- get_binder node
  case b of
    Root -> panic (text "nodeBinder of root")
    Bound b' -> return (bindBinder b')

get_binder :: (Applicative m, MonadIO m) => Node -> m (Bound Node)
get_binder node = readRef =<< nodeBound <$> nodeInfo node

set_binder :: (Applicative m, MonadIO m) => Node -> Bound Node -> m ()
set_binder node b' = do
  r <- nodeBound <$> nodeInfo node
  writeRef r b'

-- | Return the node's children.
nodeChildren :: (Applicative m, MonadIO m) => Node -> m [Node]
nodeChildren node = node_children <$> nodeInfo node

-- | Returns @True@ iff node is a\/the root.
isRoot :: (Applicative m, MonadIO m) => Node -> m Bool
isRoot node = do
  b <- getBinder node
  case b of
    Root -> return True
    _ -> return False

-- | Combine two nodes, keeping the information of the first one.
fuse :: (Applicative m, MonadIO m) => Node -> Node -> Maybe Node -> m ()
fuse keep@(Node ni1 os1) (Node ni2 os2) mb_bound = do
  bound <- get_binder (fromMaybe keep mb_bound)
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
  nsort <- nodeSort node
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
  nsort <- nodeSort node
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

nodePermissions :: (Applicative m, MonadIO m) => Node -> m Permissions
nodePermissions node = do
   bdr <- get_binder node
   case bdr of
     Bound b -> return (bindPermissions b)
     Root -> return FlexPerm

bindFlexiblyTo :: (Applicative m, MonadIO m) => Node -> Maybe Node -> m ()
bindFlexiblyTo node mb_binder = do
  set_binder node =<<
    case mb_binder of
      Nothing -> return Root
      Just n' -> do
        height' <- bindingHeight n'
        return $ Bound (BoundInfo { bindLabel = Flex
                                  , bindBinder = n'
                                  , bindPermissions = FlexPerm
                                  , bindHeight = height' + 1
                                  })

bindTo :: (Applicative m, MonadIO m) => 
          Node -> Maybe Node -> BindingLabel -> m ()
bindTo node mb_binder label = do
  set_binder node =<<
    case mb_binder of
      Nothing -> return Root
      Just n' -> do
        height' <- bindingHeight n'
        p' <- nodePermissions n'
        return $ Bound $ BoundInfo 
          { bindLabel = label
          , bindBinder = n'
          , bindPermissions = permissions_syst p' label
          , bindHeight = height' + 1
          }
        
-- | Calculate child permission based on parent permission and label.
permissions_syst :: Permissions -> BindingLabel -> Permissions
permissions_syst parent_perm label =
  case label of
    Rigid -> RigidPerm
    Flex -> if parent_perm == FlexPerm then FlexPerm else LockedPerm

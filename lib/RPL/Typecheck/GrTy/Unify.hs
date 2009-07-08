{-# LANGUAGE PatternGuards, FlexibleContexts #-}
-- | Unification of two graphical types.
--
-- (Full details are in Boris Yakobowski's PhD thesis \"Graphical Types and
-- Constraints: Second-order Polymorphism and Inference\", 2008.
-- Henceforth, referred to as [Yakobowski 2008].)
--
-- Unification of graphical types is somewhat involved because (a) it is
-- more general than standard unification and because (b) we need to update
-- the binding structure of the unified term.
--
-- Unification of graphical types is more general because we don't unify two
-- types, but we unify two /nodes within a graphical type/.  We also cannot
-- unify any two nodes, because some problems don't have principal
-- solutions.  Problems for which a principal solution exists are called
-- /admissible/.  These include in particular the following:
--
--  1. Any subset of nodes with the same (immediate) binder are allowed.
--
--  2. Any subset of nodes that are direct children of the same node.
--
--  3. Any two nodes @n1@, @n2@ where @n1 `boundAt` b@ and
--     @n2 `transitivelyBoundAt` b@.
--
--
-- Unification of graphical types works in two phases:
--
--  1. Calculate the term structure using standard unification.
--
--  2. Calculate the binding structure.
--
-- Both steps may fail.  The first step fails if the resulting term is
-- cyclic or two constructors clash.  The second step may fail if a binding
-- changed in an incompatible way.  See 'rebind' below.
-- 
module RPL.Typecheck.GrTy.Unify where

import RPL.Typecheck.GrTy.Types
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Monads
import RPL.Utils.Misc

import Control.Applicative
import Data.Unique
import Data.Maybe ( fromMaybe )
import Control.Monad ( unless, forM_, foldM, when )
import Control.Monad.Trans.Cont
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M

-- Example:
--
-- @n[v]m@ .. node n, a variable, is flexibly bound at m:
-- 
-- @n[->]=m@ .. node n, a function constructor, is rigidly bound at m.
--
-- @
--      0[->]
--     /     \
-- 1[->]=0    2[->]0
--   |       /      \
-- 3[v]0  4[->]2   5[->]2
--          |        |
--        6[->]=2  7[v]2
--          |
--        8[v]6
-- @

type Env = [()]

data UnifyError
  = Cyclic
  | ConClash Node Node
  | ForbiddenGraft NodeId [NodeId]
  | ForbiddenRaise NodeId [NodeId]
  | ForbiddenWeaken NodeId [NodeId]
  | ForbiddenMerge NodeId [NodeId]

unify :: (Applicative m, MonadIO m, MonadError String m) => 
         Env -> Node -> Node -> m ()
unify env n1 n2 = do
  tag <- liftIO $ newUnique
  bot_non_bot <- unify_struct env tag n1 n2
  virt_edges <- virtual_edges tag bot_non_bot
  rebind tag virt_edges n1
  return ()

-- | Perform structural unification of two nodes.  Keep the information of
-- the first node (if there is a choice).
--
-- When unifying two nodes, annotates the resulting node with the node IDs
-- and binders of the two original nodes that were merged.  This information
-- is used by 'rebind'.
--
-- Returns:
--
--  * A list of all the bottom nodes that were unified with a non-bottom
--    node.  The represent the /partially grafted/ nodes and needed for the
--    'rebind' step.
-- 
unify_struct :: (Applicative m, MonadIO m, MonadError String m) => 
                Env -> Unique -> Node -> Node -> m [Node]
unify_struct _env tag node1 node2 = do
    (grafts, bots) <- go ([], []) node1 node2
    whenM (hasCycle node1) $ throwError "Cyclic"
    forM_ grafts $ \(_n, tr) ->
      forM_HistTree tr $ \nid bound -> do
        case bound of
          Root -> return ()
          Bound b | FlexPerm <- bindPermissions b -> return ()
          Bound _ -> throwError $ "forbidden graft: " ++ show nid
        return ()
    return bots
  where
    -- The main worker.  Collects information on bottom nodes that were
    -- merged with non-bottom nodes:
    -- 
    --  - grafts: includes all occurrences; used for checking whether the
    --    the graft was allowed.  We could check it right away, but
    --    supposedly, for the sake of better error messages, it's better to
    --    do this check after checking for cycles.
    --
    --  - bots: does not contain duplicates.  This list will be the result
    --    of the whole function.
    --
    -- The rest is the usual unification stuff.
    -- 
    go (grafts,bots) n1 n2 = do
      equiv <- liftIO (UF.equivalent (node_info n1) (node_info n2))
      if equiv then return (grafts,bots) else do
        i1 <- liftIO $ UF.descriptor (node_info n1)
        i2 <- liftIO $ UF.descriptor (node_info n2)
        reset_unify_info tag i1
        reset_unify_info tag i2
        case (node_sort i1, node_sort i2) of
          (Bot, Bot) -> 
            (grafts, bots) <$ fuse_ n1 n2

          (_, Bot) -> do
            u2nodes <- unifiedNodes <$> readRef (nodeUnifyInfo i2)
            let grafts' = (n1, u2nodes) : grafts
            bots' <- add_bot n1 (nodeUnifyInfo i1) bots
            (grafts', bots') <$ fuse_ n1 n2
            
          (Bot, _) -> do
            u1nodes <- unifiedNodes <$> readRef (nodeUnifyInfo i1)
            let grafts' = (n1, u1nodes) : grafts
            bots' <- add_bot n2 (nodeUnifyInfo i2) bots
            (grafts', bots') <$ fuse_ n2 n1

          (TyConNode c1, TyConNode c2)
            | c1 /= c2 -> throwError "cannot unify incompatible constructors"
            | otherwise -> do
                fuse_ n1 n2
                foldM2 go (grafts, bots) (node_children i1) (node_children i2)

    -- Monadic fold over two lists at once.  Input lists must be of same
    -- length.
    foldM2 :: Monad m => (a -> b -> c -> m a) -> a -> [b] -> [c] -> m a
    foldM2 f a0 bs0 cs0 = worker a0 bs0 cs0
      where worker a [] [] = return a
            worker a (b:bs) (c:cs) = do a' <- f a b c
                                        worker a' bs cs
            worker _ _ _ = error "foldM2: arguments are not of same length"

    -- Fuse two nodes.  Keep information of first argument but record which
    -- nodes it came from in the unifyInfo
    fuse_ keep lose = do
      liftIO $ UF.union' (node_info lose) (node_info keep)
          (\lose_ni keep_ni -> do
             lose_ui <- readRef (nodeUnifyInfo lose_ni)
             modifyRef (nodeUnifyInfo keep_ni) $ \ui ->
                 ui { unifiedNodes = (Branch $! unifiedNodes ui) 
                                             $! unifiedNodes lose_ui
                    , unifyMergeHappened = True }
             return keep_ni)

    -- add node to bot_non_bot list (unless it's already in it)
    add_bot n ui_ref bots = do
      ui <- readRef ui_ref
      if not (unifyBotNonBot ui) then
        (n:bots) <$ writeRef ui_ref (ui { unifyBotNonBot = True })
       else return bots

    -- iterate over a HistTree
    forM_HistTree Empty _ = return ()
    forM_HistTree (Leaf n b) f = f n b
    forM_HistTree (Branch t1 t2) f = forM_HistTree t1 f >> forM_HistTree t2 f

reset_unify_info :: (MonadIO m) => Unique -> NodeInfo -> m ()
reset_unify_info tag ni = do
  ui <- liftIO $ readRef (nodeUnifyInfo ni)
  unless (unifyTag ui == tag) $ do
    b <- readRef (nodeBound ni)
    writeRef (nodeUnifyInfo ni) $ UnifyInfo
      { unifyTag = tag
      , unifiedNodes = Leaf (node_id ni) b 
      , unifyBotNonBot = False
      , unifyMergeHappened = False
      }

hasCycle :: (Applicative m, MonadIO m) => Node -> m Bool
hasCycle n0 = runContT (callCC go) return
  where
   go abort = do visit [] IM.empty n0
                 return False
     where
       -- Semantics of preds:
       --  - Nothing: we haven't visited the node before
       --  - Just True: we have visited the node in the current subtree
       --  - Just False: we have visited the node, but not in the current
       --                subtree
       visit preds h n = do
         nid <- nodeId n
         h' <- foldM (\h' n' -> do
                    n'id <- nodeId n'
                    case IM.lookup n'id h' of
                      Just True -> abort True
                      Just False -> return h'
                      Nothing -> visit (n:preds) h n')
                 (IM.insert nid True h) =<< nodeChildren n
         return (IM.insert nid False h')

-- | Collect the \"virtual edges\" induced by partially grafted nodes.
--
-- Assume we unify nodes @1@ and @2@ in the following type @t@:
--
-- @
--   t:            struct_unify(1,2):      virtual:
--       0[->]-             u0[->]-                 0[->]
--      /      \              | |                 /       \
--    1[v]0   2[->]0        u1[->]?            1[->]0      2[->]0
--             | |     =>     | |             /       \       \ \
--            3[->]2        u2[->]?       5[->]1     6[->]1   ....
--             | |            | |          /  \      /    \
--            4[v]2         u3[v]?     7[v]5 8[v]5  9[v]6 10[v]6
-- @
--
-- The result of structural unification is the type on the right.  In order
-- to get legally (i.e., respecting the instance relation) from the type on
-- the left to the type on the right we need to graft nodes under the
-- variable node @1@ (tree \"virtual\").
-- 
-- Note how each of these \"virtual\" nodes is flexibly bound at its
-- immediate parent.  These edges need to be considered when calculating the
-- binders for the nodes that these virtual nodes have been merged with.
-- Building the tree directly would take exponential time, however, we don't
-- need to do that.  We only need to add edges between nodes that actually
-- will appear in the result, i.e., in the example nodes @u1@, @u2@ and
-- @u3@.
--
-- The result of this function maps NodeId's to the 'Node's that it is bound
-- at.  Both refer to nodes within the unified structure.
virtual_edges :: (Applicative m, MonadIO m) => 
                 Unique  -- ^ Tag for this unification session.
              -> [Node]  -- ^ Partially grafted node (bottom nodes merged
                         -- with non-bottom nodes).
              -> m (IM.IntMap [Node])
                 -- ^ Map from node id to their virtual binders (all
                 -- with implicit binding flag 'Flex').
virtual_edges tag bot_non_bots = foldM (update Nothing) IM.empty bot_non_bots
  where
    update bound virt_edges n = do
      n_id <- nodeId n
      -- TODO: Why is this needed?
      reset_unify_info tag =<< liftIO (UF.descriptor $ node_info n)
      let (already_visited, virtual_edges_n) =
              case IM.lookup n_id virt_edges of
                Nothing -> (False, [])
                Just es -> (True, es)
--      b <- readRef (nodeBound n_info)
      let virtual_edges_n' =
              case bound of
                Nothing -> virtual_edges_n
                Just b -> b : virtual_edges_n
      let virt_edges' = IM.insert n_id virtual_edges_n' virt_edges
      if already_visited then return virt_edges'
       else foldM (update (Just n)) virt_edges' =<< nodeChildren n

unifyInfo :: (Applicative m, MonadIO m) => Node -> m UnifyInfo
unifyInfo node = do
  n_info <- liftIO $ UF.descriptor (node_info node)
  readRef (nodeUnifyInfo n_info)

-- | Calculate new bindings for the unified term.
rebind :: (Applicative m, MonadIO m, MonadError String m) => 
          Unique -> IM.IntMap [Node] -> Node -> m ()
rebind tag virt_edges node = do
  nodes <- topSort node
  mapM_ (\n -> do n_tag <- unifyTag <$> unifyInfo n
                  when (n_tag == tag) $ update_node n)
        nodes
 where
   update_node n = do
     n_id <- nodeId n
     n_info <- liftIO $ UF.descriptor (node_info n)
     unified_nodes <- unifiedNodes <$> readRef (nodeUnifyInfo n_info)
     
     let merged_with_n = 
             foldr_HistTree (\n'id bnd l ->
                                 case bnd of
                                   Root -> l
                                   Bound b -> (n'id,b) : l) [] unified_nodes

     -- See 'virtual_edges' doc for what this is.
     let virtual_binders_of_n =
             fromMaybe [] (IM.lookup n_id virt_edges)

     -- Update node binder.
     unless (null merged_with_n && null virtual_binders_of_n) $ do

       -- The new flag is the most restrictive of all the merged flags.
       -- However, we have to validate that changing the flag was actually
       -- allowed for all the nodes that @n@ has been merged with.
       let new_flag = best_flag merged_with_n

       when (new_flag == Rigid) $ do
         -- check whether we weakened a bad node
         forM_ merged_with_n $ \(n'id, b) ->
           when (bindLabel b == Flex && bindPermissions b /= FlexPerm) $
             throwError $ "forbidden weaken: " ++ show n'id ++ " " ++ show n_id

       -- The new binder is the lowest common ancestor (according to the
       -- binding relation) of all merged nodes' binding edges
       -- *and the virtual edges*.
       new_binder 
           <- do a1 <- foldM (\s (_,bi) -> addLCASet s (bindBinder bi))
                             emptyLCASet merged_with_n
                 ancestors <- foldM addLCASet a1 virtual_binders_of_n
                 lcaBinder ancestors

       -- check permissions for raising
       forM_ merged_with_n $ \(n'id, bi) -> do
         under_new_binder <- nodesEqual (bindBinder bi) new_binder
         when (not under_new_binder && bindPermissions bi == LockedPerm) $
           throwError $ "forbidden raise: " ++ show n'id ++ " " ++ show n_id

       (binder_perms, binder_height)
           <- do bnd <- getBinder n
                 case bnd of
                   Root -> return (FlexPerm, 0)
                   Bound b -> return (bindPermissions b, bindHeight b)

       setBinder n $ BoundInfo
         { bindLabel = new_flag
         , bindBinder = new_binder
         , bindPermissions = permissions_syst binder_perms new_flag
         , bindHeight = binder_height + 1
         }

   foldr_HistTree _ c Empty = c
   foldr_HistTree f c (Leaf nid b) = f nid b c
   foldr_HistTree f c (Branch l r) =
       foldr_HistTree f (foldr_HistTree f c r) l

   best_flag [] = Flex
   best_flag ((_, BoundInfo{ bindLabel = Rigid }):_) = Rigid
   best_flag ((_, BoundInfo{ bindLabel = Flex }):r) = best_flag r

-- | Return node and its children in a topologically sorted order.
topSort :: (Applicative m, MonadIO m) => Node -> m [Node]
topSort n0 = snd <$> go (IS.empty, []) n0
  where
    -- simple depth-first search
    go (visited, sorted) n = do
      n_id <- nodeId n
      if IS.member n_id visited then return (visited, sorted)
       else
         onSnd (n:) <$> (foldM go (IS.insert n_id visited, sorted) =<< nodeChildren n)
    onSnd = fmap

------------------------------------------------------------------------
-- * Lowest Common Ancestor

-- | An LCA set is a set where nodes are ordered according to their binding
-- height (and their node id as a tie-breaker).  Used by 'lcaBinder'.
newtype LCASet = LCASet (M.Map (Int, Int) Node)

emptyLCASet :: LCASet
emptyLCASet = LCASet M.empty

addLCASet :: (Applicative m, MonadIO m) => LCASet -> Node -> m LCASet
addLCASet (LCASet set) n = do
  h <- bindingHeight n
  n_id <- nodeId n
  return (LCASet $ M.insert (h, n_id) n set)

-- | Find the lowest common ancestor that binds all the nodes in the input.
--
-- This is done by repeatedly raising the lowest node until only one node is
-- left.
lcaBinder :: (Applicative m, MonadIO m) => LCASet -> m Node
lcaBinder (LCASet ancestors) = do
  let ((_,lowest_bound_node), ancestors') = M.deleteFindMax ancestors
  if M.null ancestors'
   then return lowest_bound_node
   else do
     -- By well-formedness only the root has no 'binderNode'.  That,
     -- however, means that if the largest element in the LCASet is the root
     -- then it must have been the only element and we would never reach
     -- this branch.  Also, the root is the LCA of any node, so we're
     -- guaranteed to always find a solution.
     n <- binderNode lowest_bound_node
     lcaBinder =<< addLCASet (LCASet ancestors') n

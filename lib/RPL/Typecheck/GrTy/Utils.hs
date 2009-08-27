{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module RPL.Typecheck.GrTy.Utils where

import RPL.Typecheck.GrTy.Types
import RPL.Utils.Monads
import Control.Applicative
import Control.Monad ( foldM, forM )
import Data.Array

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

-- | Return nodes in reverse post-order starting at the given root.
--
-- This is equivalent to a topological sorting of the nodes.  That is, if
-- @n@ is a child of @m@ then @reverse_post_order(m) <
-- reverse_post_order(n)@.
reversePostOrder :: (Applicative m, MonadIO m) => Node -> m (Array Int Node)
reversePostOrder n_ = do
    (_, po, ctr1) <- visit (IS.empty, [], 0 :: Int) n_
    let !ctr = ctr1 - 1
    return $ array (0, ctr) [ (ctr-i, n) | (i,n) <- po ]
  where
    visit (visited_, po, ctr_) n = do
      n_id <- nodeId n
      let !visited = IS.insert n_id visited_
      cs <- nodeChildren n
      (visited', post_order, ctr) <- foldM visit_children (visited, po, ctr_) cs
      let !post_order' = (ctr, n):post_order
      let !ctr' = ctr + 1
      return (visited', post_order', ctr')
    visit_children st@(vis, _, _) n = do
      n_id <- nodeId n
      if IS.member n_id vis then return st else visit st n

nodeToPostOrder :: (Applicative m, MonadIO m) => Array Int Node -> m (IM.IntMap Int)
nodeToPostOrder ordered = do
  po_nids <- mapM (\(po, n) -> do n_id <- nodeId n
                                  return (po, n_id))
                  (assocs ordered)
  return $ IM.fromList [ (n_id, po) | (po, n_id) <- po_nids ]

-- | Map from binder node to `[(node_id, label, sort)]`.
type InverseChildrenBinders = IM.IntMap [(Int, BindingLabel, NodeSort, Node)]

-- | A map from binder to bound nodes.
inverseChildrenBinders :: (Applicative m, MonadIO m) =>
                          Node -> m InverseChildrenBinders
inverseChildrenBinders node = do
  r <- isRoot node
  node0 <- if r then return node else binderNode node
  snd <$> (foldM go (IS.empty, IM.empty) =<< nodeChildren node0)
 where
   go (vis_,res_) n = do
     n_id <- nodeId n
     if IS.member n_id vis_ then return (vis_, res_)
      else do
        let vis = IS.insert n_id vis_
        b <- getBinder n
        case b of
          Root -> return (vis, res_)
          Bound bi -> do
            n'id <- nodeId (bindBinder bi)
            nsort <- nodeSort n
            let res = IM.alter (add_it (n_id, bindLabel bi, nsort, n)) n'id res_
            foldM go (vis, res) =<< nodeChildren n
   add_it x Nothing = Just [x]
   add_it x (Just xs) = Just (x : xs)

-- | Copy a node and its children.  Note that the original node may still be
-- a child of some other node, while the copied node will not.
copyNode :: (Applicative m, MonadIO m, MonadGen NodeId m) => Node -> m Node
copyNode node = do
  rpo <- reversePostOrder node
  let (start_node, end_node) = bounds rpo

  -- copy nodes bottom-up so we have already copied the children
  let copy_children !i copied po | i < start_node = return (po, copied)
                                 | otherwise = do
        let n = rpo ! i
        n_id <- nodeId n
        nsort <- nodeSort n
        cs <- nodeChildren n
        cs' <- forM cs $ \c -> (copied IM.!) <$> nodeId c
        n' <- newNode nsort cs'
        copy_children (i - 1) (IM.insert n_id n' copied) (n':po)

  ((node':po), copied) <- copy_children end_node IM.empty []

  copy_root_binder node' -- treated specially (can be the root)

  -- copy binders top-down, so the new permissions are correct
  let copy_binders [] _ = return ()
      copy_binders (n':n's) !i = do
        let n = rpo ! i
        Bound bi <- getBinder n -- only @node@ can be root
        b_id <- nodeId (bindBinder bi)
        case IM.lookup b_id copied of
          Nothing -> bindTo n' (Just (bindBinder bi)) (bindLabel bi)
          Just b' -> bindTo n' (Just b') (bindLabel bi)
        copy_binders n's (i + 1)

  copy_binders po (start_node + 1)

  return node'

 where
   copy_root_binder node' = do
     bdr <- getBinder node
     case bdr of
       Root -> return ()
       Bound bi -> bindTo node' (Just (bindBinder bi)) (bindLabel bi)

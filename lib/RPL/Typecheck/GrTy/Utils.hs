{-# LANGUAGE FlexibleContexts #-}
module RPL.Typecheck.GrTy.Utils where

import RPL.Typecheck.GrTy.Types
import RPL.Utils.Monads
import Control.Applicative
import Control.Monad ( foldM )
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
inverseChildrenBinders node =
  snd <$> (foldM go (IS.empty, IM.empty) =<< nodeChildren node)
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

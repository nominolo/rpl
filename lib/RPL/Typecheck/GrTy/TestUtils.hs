{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
-- | Utilities for testing only.
module RPL.Typecheck.GrTy.TestUtils where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Utils
import RPL.Typecheck.GrTy.Syntactic
import qualified RPL.Type as Typ
import qualified RPL.Names as Syn
import RPL.Utils.Monads
import RPL.Utils.Misc (foldM2, ifM)
import RPL.Utils.Pretty

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Control.Monad ( foldM, when, forM_, forM )
import Control.Monad.Trans.Cont
import Data.STRef
import Control.Applicative
import Data.Maybe ( fromMaybe, isJust )
import Data.Supply
import Data.List ( nub )
--import Data.Array.IArray
import Data.Array.ST
import Data.Array.Unboxed
import System.Cmd
import System.FilePath ( (<.>) )
import System.Directory ( getTemporaryDirectory )
import System.IO
--import Debug.Trace

newtype M a = M (StrictStateErrorT (Supply NodeId) String IO a)
    deriving (Functor, Applicative, Monad,
              MonadError String, MonadState (Supply NodeId), MonadIO)

instance MonadGen NodeId M where getSupply = get; setSupply = put

runM :: M a -> IO a
runM (M act) = do
  s <- newNumSupply
  r <- runStrictStateErrorT act s
  case r of
    Left err -> fail err
    Right (a,_) -> return a

-- | A one-step grafting of a constructor type.
--
-- Replaces the node (which must be a bottom node with flexible permissions)
-- with a constructor type.  A constructor type is a constructor node where
-- all children are variables flexibly bound at the constructor node.  A
-- graft step with @->@ as the constructor therefore looks like:
--
-- >   x[v]y   =>   x[->]y
-- >               /      \
-- >           x1[v]x   x2[v]x
--
-- Returns @True@ iff grafting was possible. 
graft1 :: (Applicative m, MonadIO m, MonadGen NodeId m) =>
          Node -> Typ.TyCon -> m Bool
graft1 node tycon = do
  let arity = Typ.tyConArity tycon
  perms <- nodePermissions node
  nsort <- nodeSort node
  bndr <- getBinder node
  if (perms /= FlexPerm || nsort /= Bot)
   then dump "not flexible" >> return False
   else do
    children <- sequence (replicate arity (newNode Bot []))
    node' <- newNode (TyConNode tycon) children
    mapM_ (\n -> bindTo n (Just node') Flex) children
    dump . show =<< (,) <$> nodeId node <*> nodeId node'
    fuse node' node Nothing
    case bndr of
      Root -> return ()
      Bound bi -> bindTo node (Just (bindBinder bi)) (bindLabel bi)
    return True
 where dump msg = return () -- liftIO (putStrLn $ "graft1: " ++ msg)

-- | A one-step raising.
--
-- Raises the node's binder by one level (if possible).
raise1 :: (Applicative m, MonadIO m) =>
          Node 
       -> m Bool -- ^ @True <=>@ raising was possible. 
raise1 node = do
  b <- getBinder node
  case b of
    Root -> return False
    Bound bi
     | bindPermissions bi == LockedPerm -> return False
       -- TODO: allow inert/monomorphic nodes
     | otherwise -> do
        let n' = bindBinder bi
        b' <- getBinder n'
        case b' of
          Root -> return False
          Bound bi' -> do
            bindTo node (Just (bindBinder bi')) (bindLabel bi)
            return True

-- | Turns a flexible edge into a rigid edge.  Node must have flexible
-- permissions.
weaken1 :: (Applicative m, MonadIO m) =>
           Node 
        -> m Bool -- ^ @True <=>@ weakening was possible.
weaken1 node = do
  b <- getBinder node
  case b of
    Root -> return False
    Bound bi
      -- Weakening a rigid node is not possible since by definition (of
      -- permissions) its binding edge is rigid.  If the binding edge is
      -- flexible and the node doesn't have flexible permissions, then it
      -- must be locked and hence cannot be weakened.
      --
      -- TODO: allow inert/monomorphic nodes
      | bindPermissions bi /= FlexPerm
        || bindLabel bi /= Flex -> return False
      | otherwise -> do
         setBinder node bi{ bindLabel = Rigid, bindPermissions = RigidPerm }
         recomputePermissions node
         return True

-- | Merge the two nodes.  Result is @Just indirects@ iff merging was
-- possible and @indirects@ is a pair of nodes that were indirectly merged.
merge1 :: (Applicative m, MonadIO m) =>
          Node -> Node -> m (Maybe [(Node, Node)])
merge1 n1_ n2_ = do
  b1 <- getBinder n1_
  b2 <- getBinder n2_
  case (b1, b2) of
    (Root, Root) -> 
        dump "root|root" >> return Nothing -- cannot merge two roots
    (Bound bi1, Bound bi2)
      | bindBinder bi1 == bindBinder bi2,
        bindLabel bi1 == bindLabel bi2,
        bindPermissions bi1 /= LockedPerm, 
        bindPermissions bi2 /= LockedPerm -> do
          congr <- locallyCongruent n1_ n2_
          if congr then Just <$> do_merge [] n1_ n2_
            else dump "non-congr" >> return Nothing
      | otherwise ->
         dump ("bad-binders/perms" ++ show (bindBinder bi1 == bindBinder bi2,
                                            bindLabel bi1 == bindLabel bi2,
                                            bindPermissions bi1 /= LockedPerm, 
                                            bindPermissions bi2 /= LockedPerm) )
          >> return Nothing
 where
   do_merge acc n1 n2 = do
     eq <- nodesEqual n1 n2
     if eq then return acc else do
      cs1 <- nodeChildren n1
      cs2 <- nodeChildren n2
      fuse n1 n2 Nothing
      foldM2 do_merge ((n1,n2):acc) cs1 cs2
   dump msg = liftIO $ putStrLn ("merge1:" ++ msg)

-- | Two nodes are /congruent/ (w.r.t. a term graph) if they are distinct and:
--
--  1. all respective children have the same constructors, and
--
--  2. the amount of sharing is the same.

-- Implementation: The above implies that we can construct a one-to-one
-- mapping from @n1@'s children to @n2@'s children.  If a mapping already
-- exists it must be the same mapping, if it doesn't, add it.
--
-- This mapping actually describes which nodes will get merged with which
-- other nodes.
congruent :: (Applicative m, MonadIO m) => Node -> Node -> m Bool
congruent n1_ n2_ =
   runContT (callCC (\abort -> do _ <- go abort (IM.empty, IM.empty) n1_ n2_
                                  return True))
            return
  -- TODO: use breadth-first traversal
 where
   go abort mappings@(m1,m2) n1 n2 = do
     ni1 <- nodeInfo n1
     ni2 <- nodeInfo n2
     let id1 = unNodeId $ node_id ni1
         id2 = unNodeId $ node_id ni2
     if id1 == id2 then return (IM.insert id1 id1 m1, IM.insert id2 id2 m2)
      else do
       if (node_sort ni1 /= node_sort ni2) then abort False else do
         mappings' 
           <- case (IM.lookup id1 m1, IM.lookup id2 m2) of
                (Nothing, Nothing) -> 
                    return (IM.insert id1 id2 m1, IM.insert id2 id1 m2)
                (Just i1', Just i2') | i1' == id2 && i2' == id1 ->
                    return mappings
                _ -> abort False
         foldM2 (go abort) mappings' (node_children ni1) (node_children ni2)

-- | Two nodes @n1@ and @n2@ of a type graph @t@ are /locally congruent/ if:
--
--  1. @n1@ and @n2@ are congruent in the term graph @g@ underlying @t@.
--
--  2. the binding edges under @n1@ and @n2@ are compatible with the term
--     graph @g[n1=n2]@ (the term graph where @n1@ and @n2@ are merged).
--     TODO: what does "compatible" mean here?
--
--     That is, if n1' and n2' are indirectly merged, they must have the
--     same (possibly merged) binder and binding labels.
--
--  3. for any two distinct nodes @n1'@ and @n2'@ under @n1@ and @n2@
--     respectively, if @n1'@ and @n2'@ are merged in @g[n1=n2]@, then @n1'@
--     and @n2'@ are bound below @n1@ and @n2@.  I.e., no binding edges
--     above @n1@ and @n2@ can be merged.
--
-- Two term graph nodes are /congruent/ if they have the same constructors
-- and the same amount of sharing.
locallyCongruent :: (Applicative m, MonadIO m) =>
                    Node -> Node -> m Bool
locallyCongruent n1_ n2_ =
  runContT (callCC (\abort -> do go0 abort n1_ n2_
                                 return True))
           (\x -> return x)
 where
   dump txt = liftIO $ return () -- putStrLn ("..lc:" ++ txt)

   go0 abort n1 n2 = do
     ni1 <- nodeInfo n1
     ni2 <- nodeInfo n2
     let id1 = unNodeId $ node_id ni1
         id2 = unNodeId $ node_id ni2
     if id1 == id2 then return (IM.empty, IM.empty) else do
       b1 <- getBinder n1
       b2 <- getBinder n2
       case (b1,b2) of
         (Root, Root) -> return ()
         (Bound bi1, Bound bi2) -> do
           eq <- nodesEqual (bindBinder bi1) (bindBinder bi2)
           if not eq then dump "non-matching-binder" >> abort False >> return ()
            else return ()
         _ -> dump "WrongBinder" >> abort False >> return ()
       foldM2 (go abort) (IM.singleton id1 id2, IM.singleton id2 id1)
              (node_children ni1) (node_children ni2)

   -- m1 and m2 are mappings from a node to the node it got merged with.  m1
   -- contains the n1 -> n2 mapping, m2 the other way around.
   --
   -- INVARIANT: m1/m2 contain mappings for each visited node
   go abort mappings@(m1, m2) n1 n2 = do
     ni1 <- nodeInfo n1
     ni2 <- nodeInfo n2
     let id1 = unNodeId $ node_id ni1
         id2 = unNodeId $ node_id ni2
     dump (show id1 ++ ":" ++ show id2)
     if id1 == id2 then return (IM.insert id1 id1 m1, IM.insert id2 id2 m2)
      else do
       if node_sort ni1 /= node_sort ni2 
        then dump "ConstrMismatch" >> abort False else do
         mappings' 
           <- case (IM.lookup id1 m1, IM.lookup id2 m2) of
                (Nothing, Nothing) -> 
                    return (IM.insert id1 id2 m1, IM.insert id2 id1 m2)
                (Just i1', Just i2') | i1' == id2 && i2' == id1 ->
                    return mappings
                _ -> dump "MappingMismatch" >> abort False
         dump "mappings ok"
         b1 <- getBinder n1
         b2 <- getBinder n2
         case (b1,b2) of
           (Root, Root) -> return ()
           (Bound bi1, Bound bi2)
             | bindLabel bi1 == bindLabel bi2
               {- TODO: do we need this?
                  && bindPermissions bi1 == bindPermissions bi2 -} -> do
               let n1' = bindBinder bi1
                   n2' = bindBinder bi2
               -- The only admissible case is if n1' and n2' will be merged
               -- (or are the same node) and they are bound under n1 and n2,
               -- respectively.  Assuming the graph is well-formed and
               -- because we are performing a top-down traversal, then this
               -- is the case iff we have visited n1'/n2'.
               n1'id <- nodeId n1'
               n2'id <- nodeId n2'
               case IM.lookup n1'id m1 of
                 Nothing -> -- not visited
                     dump "bound-above" >> abort False >> return ()
                 Just n' | n' == n2'id -> return () -- Yay!
                         | otherwise ->
                             -- visited but not merged with / identical to n2'
                             dump "non-merged-binder" >> abort False >> return ()
             
           _otherwise -> dump "RootNonRoot" >> abort False >> return ()
         foldM2 (go abort) mappings' (node_children ni1) (node_children ni2)

-- | A node @n@ is inert if all polymorphic nodes transitively bound under
-- @n@ are protected by a rigid edge.
--
-- This includes in particular monomorphic nodes that don't bind any node.
isInert :: Int -> InverseChildrenBinders -> Bool
isInert n0 bound_at_n =
  all rigid_or_monomorphic $ fromMaybe [] $ IM.lookup n0 bound_at_n
 where
   rigid_or_monomorphic (_, Rigid, _, _) = True
   rigid_or_monomorphic (_, Flex, Bot, _) = False
   rigid_or_monomorphic (n, _, _, _) = 
     all rigid_or_monomorphic $ fromMaybe [] $ IM.lookup n bound_at_n


dotty_cmd = "dot"
open_png = "open"

trans_close :: [Node] -> IM.IntMap Node -> IO (IM.IntMap Node)
trans_close [] res = return res
trans_close (r:rs) res = do
  r_id <- nodeId r
  if IM.member r_id res
   then trans_close rs res
   else do
     r's <- nodeChildren r
     trans_close (r's ++ rs) (IM.insert r_id r res)

dottyNode :: Node -> IO ()
dottyNode n = do
  nodes <- trans_close [n] IM.empty
  nlines <- mapM ppNode (IM.elems nodes)
  let dotty_descr = header ++ unlines nlines ++ footer
  tmp_dir <- getTemporaryDirectory
  (path, h) <- openTempFile tmp_dir "dotdump"
  hPutStr h dotty_descr
  hFlush h
  hClose h
  let out = path <.> "png"
  rawSystem dotty_cmd ["-Tpng", "-o", out, path ]
  rawSystem open_png [out] 
  return ()
 where
    header = unlines ["digraph tygraph {"
                     ,"\tgraph[fontsize=14, fontcolor=black, color=black];" -- , ordering=\"out\"];"
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
                        ++ " [dir=back, constraint=" ++ (if True then "true" else "false") 
                        ++ ", style=" ++ 
                        (case bindLabel b of
                           Flex -> "dotted"
                           Rigid -> "dashed") ++
                        "];"])
      let colour = case bdr of
                     Root -> ", color=green"
                     Bound bi ->
                       case bindPermissions bi of
                         FlexPerm -> ", color=green"
                         RigidPerm -> ", color=orange"
                         LockedPerm -> ", color=red"
      return $ unlines $
         [ "\t" ++ show i ++ " [label=" ++ show (show i ++ " " ++ ppSort s) ++ 
           (if r then ",shape=doublecircle" else "") 
           ++ colour
           ++ "];" ] ++ 
         [ "\t" ++ show i ++ " -> " ++ show c ++ " [label=" ++ show (show m) ++ "];" 
            | (c,m) <- zip ch [(1::Int)..] ]
         ++ bind_edge

ppSort :: NodeSort -> String
ppSort (TyConNode tc) = Syn.idString (Typ.tyConName tc)
ppSort (TypeNode _)  = "T"
ppSort Bot           = "v"
ppSort (Forall _)    = "G"

type Path = [Int]

data InstOp
  = Graft Path Typ.TyCon
  | Raise Path
  | Weaken Path
  | Merge Path Path
  deriving Show

-- a queue for breadth-first traversal
-- INVARIANT: first field is @[]@ @==>@ second field @[]@
data Queue a = Queue [a] [a]

emptyQueue :: Queue a
emptyQueue = Queue [] []

singletonQueue :: a -> Queue a
singletonQueue a = Queue [a] []

unconsQueue :: Queue a -> Maybe (a, Queue a)
unconsQueue (Queue [] _) = Nothing
unconsQueue (Queue (x:xs) r) = Just (x, ensureQInv $ Queue xs r)

ensureQInv :: Queue a -> Queue a
ensureQInv (Queue [] r) = Queue (reverse r) []
ensureQInv q = q

snocNQueue :: Queue a -> [a] -> Queue a
snocNQueue (Queue [] _r) as = Queue as [] -- by invariant _r = []
snocNQueue (Queue hs r) as = Queue hs (reverse as ++ r)

queueToList :: Queue a -> [a]
queueToList (Queue hs ts) = hs ++ reverse ts

infix 1 <?

-- | @t <? t'@ returns @Just ops@ iff @t'@ is an instance of @t@.  @ops@ is
-- a witness of the instance relation.  Applying the operations in @ops@ (in
-- order) on @t@ will yield a type-graph identical to @t'@ up to node ids.
--
-- Currently only works on root nodes.

-- See Note [Instance]
(<?) :: (Applicative m, MonadIO m, MonadGen NodeId m) =>
        Node -> Node -> m (Maybe [InstOp])
(<?) n1__ n2_ = do
   r1 <- isRoot n1__
   r2 <- isRoot n2_
   if not (r1 && r2) then error "Non-root given to (<?)" else do
   n1_ <- copyNode n1__
   runContT
     (callCC $ \abort -> do
        ops_ <- go (\msg -> dump msg >> abort Nothing)
                  (singletonQueue (n1_,[],n2_,[]))
                  (IM.empty, IM.empty, [], [])
        let ops = reverse ops_
        dump "checking instance"
        ok <- checkInstance n1__ n2_ ops
        if ok then return (Just ops) else return Nothing)
     return
  where
    -- Breadth-first top-down traversal to determine the graftings.  We use
    -- a queue to implement this.
    -- 
    --  - l2r is the mapping from left-hand-side (lhs) node ids to rhs
    --    nodes.  After grafting, instance operations can only decrease the
    --    number of nodes hence l2r can only contain one mapping from lhs to
    --    rhs nodes.
    --    
    --  - r2l is a mapping from nodes on the rhs to one or more nodes on the
    --    lhs.  All the lhs nodes must eventually be merged into the same
    --    nodes.
    --
    --  - vis records the nodes in the inverse order in which we visited them.
    --    This is used to perform a breadth-first bottom-up traversal for
    --    determining raisings and merge/weakenings.
    --
    --  - ops is the accumulator for the operations performed so far.
    --
    go abort q0 (l2r, r2l, vis0, ops) 
     | Just ((n1,p1,n2,p2),q') <- unconsQueue q0 = do
      ni1 <- nodeInfo n1
      ni2 <- nodeInfo n2
      let id1 = unNodeId $ node_id ni1
          id2 = unNodeId $ node_id ni2
      qis <- mapM nodeId [ n | (n,_,_,_) <- queueToList q' ]
      dump $ "visiting: " ++ show (id1, id2, p1, p2, qis)
      -- Always add the node to visited nodes -- even if already visited --
      -- because we want to retain the *latest* time we traversed the node.
      -- See Note [Bottom-Up Traversal]
      let !vis = (n1, reverse p1) : vis0
      case IM.lookup id1 l2r of
        Just _ -> do
          -- already visited
          dump $ "already visited: " ++ show id1
          go abort q' (l2r, r2l, vis, ops)
        Nothing -> do
          case (node_sort ni1, node_sort ni2) of
            (Bot, Bot) -> do
              let l2r' = IM.insert id1 n2 l2r
                  r2l' = IM.insertWith (++) id2 [(n1, reverse p1)] r2l
              go abort q' (l2r', r2l', vis, ops)

            (_, Bot) -> 
              -- a bottom node can never be an instance of something other
              -- than a bottom node.
              abort "bot is never instance of non-bot" >> return undefined

            (Bot, TyConNode tc) -> do
              dump $ "bot_non_bot" ++ show id1
              -- TODO: check permissions on bottom node
              ok <- graft1 n1 tc
              if not ok then abort "graft permission error" >> return undefined else do
               id1' <- nodeId n1 -- may have changed
               dump $ "new node id: " ++ show id1 ++ "->" ++ show id1'
               cs1 <- nodeChildren n1
               let cs2 = node_children ni2
               let l2r' = IM.insert id1' n2 l2r
                   r2l' = IM.insertWith (++) id2 [(n1, reverse p1)] r2l
                   ops' = Graft (reverse p1) tc : ops
                   q'' = snocNQueue q' [ (c1, c:p1, c2, c:p2) |
                                          (c, c1, c2) <- zip3 [1..] cs1 cs2 ]
               go abort q'' (l2r', r2l', vis, ops')

            (TyConNode tc1, TyConNode tc2) | tc1 == tc2 -> do
              let l2r' = IM.insert id1 n2 l2r
                  r2l' = IM.insertWith (++) id2 [(n1, reverse p1)] r2l
                  cs1 = node_children ni1
                  cs2 = node_children ni2
                  q'' = snocNQueue q' [ (c1, c:p1, c2, c:p2) |
                                          (c, c1, c2) <- zip3 [1..] cs1 cs2 ]
              go abort q'' (l2r', r2l', vis, ops)

            _ -> abort "non-matching constructors" >> return undefined

    -- We traversed all nodes top-down and breadth-first (left to right).
    -- `vis` will now contain the nodes we traversed in the inverse order,
    -- i.e., bottom-up right to left.  This is exactly the order we need for
    -- checking for raisings, weakenings and merges.
    go abort _ (l2r, r2l_, dnodes, ops_) = do
       let nodes = nub dnodes
       ops' <- foldM check_raise ops_ nodes
       fst <$> foldM check_weaken_merge (ops', r2l_) nodes
      where
        check_raise ops (n, p) = do
          n_id <- nodeId n
          dump $ "check_raise: " ++ show n_id
          let Just target = IM.lookup n_id l2r
          n_binder <- getBinder n
          t_binder <- getBinder target
          case (n_binder, t_binder) of
            (Root, Root) -> return ops
            (Bound bi, Bound bi') -> do
              bid <- nodeId (bindBinder bi)
              let Just target_binder = IM.lookup bid l2r
              t_bid <- nodeId target_binder
              t_bid' <- nodeId (bindBinder bi')
              if t_bid == t_bid' then return ops else do
               dump $ show (l2r, r2l_)
               dump $ show (bi, bi')
               dump $ "raising " ++ show n_id
               ok <- raise1 n
               --dotty_progress
               if not ok then abort "no raise allowed" >> return undefined else
                 check_raise (Raise p : ops) (n, p)
            _ -> abort "root and non-root raise" >> return undefined

        check_weaken_merge (ops0, r2l) (n, p) = do
          n_id <- nodeId n
          n_bndr <- getBinder n
          let Just n_target = IM.lookup n_id l2r
          t_id <- nodeId n_target
          let Just merge_with = IM.lookup t_id r2l
          ops <- maybe_weaken n p ops0
          case merge_with of
            [_] -> do
              dump $ "skipping_merge: " ++ show (n_id, p)
              return (ops, r2l)
            _ -> do
              perm <- nodePermissions n
              case perm of
                LockedPerm ->
                  return (ops, r2l)
                _ -> do
                  mids <- mapM (\(n',p') -> do n'id <- nodeId n'
                                               return (n'id, p'))
                               merge_with
                  dump $ "trying_merges: " ++ show (n_id, p) ++ show mids
                  try_merges n p n_bndr t_id (ops, r2l) [] merge_with

        maybe_weaken n p ops0 = do
          n_id <- nodeId n
          let Just n_target = IM.lookup n_id l2r
          n_bndr <- getBinder n
          t_bndr <- getBinder n_target
          case (n_bndr, t_bndr) of
            (Root, Root) -> return ops0
            (Bound bi, Bound bi')
              | bindLabel bi == Flex && bindLabel bi' == Rigid -> do
                  dump $ "weakening: " ++ show n_id
                  ok <- weaken1 n
                  dotty_progress
                  if not ok then abort "could not weaken" >> return undefined else
                    return (Weaken p : ops0)
              | otherwise -> return ops0  -- not needed
              -- case cannot happen, check_raise would have bailed

        try_merges n p (Bound bi) t_id (ops, r2l) unmerged n's =
           go_merge ops unmerged n's
         where
          go_merge ops unmerged [] =    
            return (ops, IM.insert t_id unmerged r2l)
          go_merge ops unmerged ((n',p'):n's) = do
            eq <- nodesEqual n n'
            if eq then do dump $ "-eq:" ++ show (p,p') 
                          go_merge ops ((n',p'):unmerged) n's
             else do
              b' <- binderNode n'  -- roots can never be merged, so this is fine
              if b' /= bindBinder bi then do dump $ "-bad-bnd:" ++ show (p,p')
                                             go_merge ops ((n',p'):unmerged) n's
               else do
                congr <- locallyCongruent n n'
                if not congr then do dump $ "-not-congr:" ++ show (p,p')
                                     go_merge ops ((n',p'):unmerged) n's
                 else do
                  ops <- maybe_weaken n' p' ops
                  n_id <- nodeId n
                  n'id <- nodeId n'
                  dump $ "merging: " ++ show (n_id,p) ++ "|" ++ show (n'id,p')
                  ind <- merge1 n n'
                  dotty_progress
                  case ind of
                    Nothing -> abort "merge1 failed" >> return undefined
                    Just _ -> -- XXX: propagate indirect merge info
                      go_merge (Merge p p' : ops) unmerged n's
    
    --dump msg = liftIO $ putStrLn $ "inst: " ++ msg
    dump _msg = return ()
    dotty_progress = liftIO $ return () --dottyNode n1_


{-
Note [Instance]
---------------

While there are many instance steps possible, any instance relation can be
arranged into the following form and therefore describe a canonical instance
relation witness:

 1. Perform all graftings first, it is sufficient that each grafting is a
    constructor type grafting.

 2. Perform all raisings in a bottom-up ordering.

 3. Perform all weakings and mergings bottom-up in an interleaved ordering where
    a weaking on a node @n@ must occur before any merges on the same node.

Raisings, graftings and merge-weakenings commute:

 * Let @t <? t'@.  Let @n@ be a bottom node in @t@ and non-bottom in @t'@
   Let @ct_n@ be the construct or type of n in @t'@.  Then following
   relation holds:

   > t <? Graft(n, ct_n)(t) <? t'

 * Let @t <? t'@.  Let @n@ be a node such that @tr = Raise(n)(t)@ for some @tr@
   and @n@ has a different binder in @t@ and @t'@.  Then @Raise(n)(t) <? t'@.


Note [Bottom-Up Traversal]
--------------------------

Consider the graph where the nodes are labelled in their top-down
breadth-first order.

     0
     |\
     | 2
     |/ |
     1  5
     |\ \\
     3 '-4

The proper bottom-up traversal is *not* `[5,4,3,2,1,0]` but `[4,3,5,1,2,0]`

XXX: Hm, even the breadth-first order doesn't seem correct...

-}


checkInstance :: (Applicative m, MonadIO m, MonadGen NodeId m) =>
                 Node -> Node -> [InstOp] -> m Bool
checkInstance nleft_ nright ops_ = do 
   runContT
     (callCC $ \abort -> do
        nleft <- copyNode nleft_
        dump $ "copied left node"
        --liftIO $ dottyNode nleft
        nleft' <- go (abort False) nleft ops_
        dump $ "checking for congruence"
        congr <- locallyCongruent nleft' nright
        if congr then return True else return False)
     return
 where
   go abort n [] = dump "huh?" >> return n
   go abort n (o:os) = do 
     dump $ "checking " ++ show o
     check_op o
     go abort n os
    where
     check_op (Graft p tc) = do
       n' <- node_at_path n p
       ok <- graft1 n' tc
       if ok then return () else abort
     check_op (Raise p) = do
       n' <- node_at_path n p
       ok <- raise1 n'
       if ok then return () else abort
     check_op (Weaken p) = do
       n' <- node_at_path n p
       ok <- weaken1 n'
       if ok then return () else abort
     check_op (Merge p1 p2) = do
       n1 <- node_at_path n p1
       n2 <- node_at_path n p2
       ind <- merge1 n1 n2
       if isJust ind then return () else abort
 
   dump msg = return () --liftIO (putStrLn msg)
   
   node_at_path n [] = do n_id <- nodeId n; dump $ "path node " ++ show n_id; return n
   node_at_path n (i:is) = do
     n' <- (!! (i-1)) <$> nodeChildren n
     node_at_path n' is

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

{-
    n <- fst <$> runStateT (go node) (IM.empty, IM.empty)
    recomputePermissions n
    return n
  where
    ifVisited n m m2 = do
      n_id <- nodeId n
      visited <- gets fst
      case IM.lookup n_id visited of
        Just n' -> m n'
        Nothing -> do
          n' <- m2
          modify (\(_,bs) -> (IM.insert n_id n' visited, bs))
          return n'
    go n = 
      ifVisited n return $ do
        cs <- nodeChildren n
        cs' <- mapM go cs
        n_sort <- nodeSort n
        n' <- newNode n_sort cs'
        add_binder n' =<< getBinder n
        do_binds n' n
        return n'
    add_binder _ Root = return ()
    add_binder n (Bound bi) = do
      b_id <- nodeId (bindBinder bi)
      modify $ \(vis, bs) -> (vis, IM.insertWith (++) b_id [(n, bindLabel bi)] bs)
    do_binds n' n = do
      n_id <- nodeId n
      bind_here <- gets (fromMaybe [] . IM.lookup n_id . snd)
      forM_ bind_here $ \(m, l) -> bindTo m (Just n') l
-}
-- | The first component is the IDom information in terms of the node's
-- reverse post-order (RPO) number.  E.g., if node @n@ has RPO number @3@
-- and node @m@ is the immediate dominator of @n@ and its RPO number is @1@
-- then @idom ! 3 == 1@.
--
-- The second component maps from RPO number to the respective nodes.
type IDomResult = (UArray Int Int, Array Int Node)

-- | Compute the immediate dominators
idoms :: (Applicative m, MonadIO m) => Node -> m IDomResult
idoms n0 = do
  -- This uses the algorithm described in the paper ["A Simple, Fast
  -- Dominance Algorithm" by K. D. Cooper, T. J. Harvey and Ken Kennedy].
  -- The algorithm is simpler than Tarjan/Lengauer and according to the
  -- paper more efficient on smaller graphs (< 30K nodes).  (They use
  -- "typical" control flow graphs, though, so this may not be a good
  -- general use case.)  We use it here mainly for its simplicity.
  rpo <- reversePostOrder n0
  npo <- nodeToPostOrder rpo
  preds <- invertEdges rpo npo
  let (start_node, last_node) = bounds rpo
  -- the core algorithm
  let doms = runSTUArray $ do
        doms <- newArray (bounds rpo) unk
        writeArray doms start_node start_node;
        changed <- newSTRef True;
        whileM (readSTRef changed) $ do
          writeSTRef changed False
          forM_ [1..last_node] $ \b -> do
            let Just (new_idom0, ps) = IS.minView (preds ! b)
            -- new_idoms is necessarily already processed since it is the
            -- smallest predecessor (in rev. post-order numbering) and we traverse
            -- the graph in increasing reverse post-order.
            let mb_intersect n_idom p = do
                  d <- readArray doms p
                  if d == unk then return n_idom else intersect doms p n_idom
            new_idom <- foldM mb_intersect new_idom0 (IS.toList ps)
            old_idom <- readArray doms b
            when (new_idom /= old_idom) $ do
              writeArray doms b new_idom
              writeSTRef changed True
        return doms
  return (doms, rpo)
 where
   -- inverted children edges with node's post-order as id
   -- result :: Array Int IS.IntSet
   invertEdges ns n2po = do
     idxs <- forM (elems ns) $ \n -> do
               n_rpo <- (n2po IM.!) <$> nodeId n
               cs <- nodeChildren n
               forM cs $ \c -> do
                 c_rpo <- (n2po IM.!) <$> nodeId c
                 return (c_rpo, IS.singleton n_rpo)
     return (accumArray (IS.union) IS.empty (bounds ns) (concat idxs) :: Array Int IS.IntSet)

   unk = (-1) :: Int

   intersect doms b1 b2 = go b1 b2
     -- At the latest, stops at the start node (if neither arg is == unk)
     where go finger1 finger2
             | finger1 == finger2 = return finger1
             | finger1 > finger2 = do finger1' <- readArray doms finger1
                                      go finger1' finger2
             | otherwise = do finger2' <- readArray doms finger2
                              go finger1 finger2'

   whileM c m = do b <- c; if b then m >> whileM c m else return ()

type IDomMap = IM.IntMap Node

mkIDomMap :: (Applicative m, MonadIO m) => IDomResult -> m IDomMap
mkIDomMap (doms, rpo) = do
  let (start_node, last_node) = bounds rpo
  foldM build_result IM.empty [start_node .. last_node]
 where 
   build_result m b = do
     let node = rpo ! b
     let idom = rpo ! (doms ! b)
     n_id <- nodeId node
     return (IM.insert n_id idom m)

-- | Depth-first traversal for side effect only.
dfs_traverse :: (Applicative m, MonadIO m) =>
                (Node -> m ()) -> Node -> m ()
dfs_traverse f n_ = go IS.empty n_ >> return ()
  where
    go visited n = do
      n_id <- nodeId n
      if IS.member n_id visited then return visited else do
       f n
       foldM go (IS.insert n_id visited) =<< nodeChildren n

-- | Traverse the graph in depth-first order collecting some result.
dfs_collect :: (Applicative m, MonadIO m) => 
               a -> (a -> a -> a) -> (Node -> m a) -> Node -> m a
dfs_collect z c f n_ = fst <$> go IS.empty n_
  where
    go visited n = do
      n_id <- nodeId n
      if IS.member n_id visited then return (z, visited) else do
       r <- f n
       go_many r (IS.insert n_id visited) =<< nodeChildren n
    go_many r visited [] = return (r, visited)
    go_many r visited (n:ns) = do
      (r', visited') <- go visited n
      let r'' = r `c` r'
      r'' `seq` go_many r'' visited' ns

-- | Return all the node's children which allow graftings.
graftables :: (Applicative m, MonadIO m) => Node -> m [Node]
graftables = dfs_collect [] (++) flex_var
  where
    flex_var n = do
      n_sort <- nodeSort n
      n_perms <- nodePermissions n
      if n_sort == Bot && n_perms == FlexPerm then return [n] else return []
      

{-
bfs_traverse :: (Applicative m, MonadIO m) =>
                (Node -> m ()) -> Node -> m ()
bfs_traverse f n_ = go IS.empty n_ Anil
 where
   go visited n next = do
     n_id <- nodeId n
     if IS.member n_id visited then k visited else do
       f n
       go_children (IS.insert n_id visited) k =<< nodeChildren n

   go_next v Anil = return v
   go_next v (Anode x) = go v Anil
   go_next v (Anodes xs) = go_list v xs
   go_next v (Aconc a1 a2) = do 
     v' <- go_next v a1
     go_next v' a2
   go_list v [] = return v
   go_list v (x:xs) = do v' <- go v x; go_list 
--   go_childern 
-}

-- | Ensure that binder meta-information is correct.  This can happen if binders
-- aren't constructed in a top-down order.
recomputePermissions :: (Applicative m, MonadIO m) => Node -> m ()
recomputePermissions = dfs_traverse recomp
 where
   recomp n = do
     b <- getBinder n
     case b of
       Root     -> bindTo n Nothing Flex
       Bound bi -> bindTo n (Just (bindBinder bi)) (bindLabel bi)

wellformed :: (Applicative m, MonadIO m) => Node -> m Bool
wellformed node = do
  (doms, rpo) <- idoms node
  let (start_node, end_node) = bounds rpo
  let go i | i > end_node = return True
           | otherwise = do ok <- dominatedByBinder i (rpo ! i)
                            if ok then go $! (i + 1) else return False
      dominatedByBinder i n = do
        bdr <- getBinder n
        case bdr of
          Root -> return False  -- only start_node may be the root
          Bound bi -> do
            ok <- isDom doms rpo i (bindBinder bi)
            when (not ok) $ report_dom_error n bi
            return ok
  go (start_node + 1)
 where
   isDom doms rpo i b = do
     let j = doms ! i
     if i == j then return False else do
       eq <- nodesEqual (rpo ! j) b
       if eq then return True else isDom doms rpo j b

   report_dom_error n bi = return ()
--    report_dom_error n bi = do
--      n_id <- nodeId n
--      b_id <- nodeId (bindBinder bi)
--      liftIO $ putStrLn $ show n_id ++ " is not dominated by its binder, " ++ show b_id

ex1 :: IO ()
ex1 = runM $ do
  n4 <- new_bot
  n2 <- new_fun n4 n4
  n9 <- new_bot
  n7 <- new_fun n9 n9
  n5 <- new_fun n7 n7
  n8 <- new_bot
  n6 <- new_fun n8 n8
  n3 <- new_fun n5 n6
  n1 <- new_fun n2 n3
  bind_rigid n2 n1
  bind_flex n4 n1
  bind_flex n3 n1
  bind_flex n5 n3
  bind_flex n6 n3
  bind_rigid n7 n3
  bind_flex n8 n3
  bind_flex n9 n7

  ne <- new_bot
  nd <- new_fun ne ne
  nc <- new_fun nd nd
  nb <- new_fun nc nc
  na <- new_fun nb nb
  bind_flex nc na
  bind_rigid nb na
  bind_rigid nd na
  bind_flex ne nd

  k1 <- new_bot
  k2 <- new_fun k1 k1
  k3 <- new_fun k2 k1
  bind_flex k1 k3
  bind_flex k2 k3

  h1 <- new_bot
  h2 <- new_fun h1 h1
  h3 <- new_fun h2 h1
  bind_flex h2 h3
  bind_flex h1 h2

{-
  m1 <- new_bot
  m2 <- new_bot
  m3 <- new_fun m2 m2
  bind_flex m2 m3

  x1 <- new_bot
  x2 <- copyNode x1
  graft1 x2 Typ.funTyCon
  liftIO $ dottyNode x1
  liftIO $ dottyNode x2
  ok <- x1 <? x2
  liftIO $ print ok
  -}
--   let nn = k3
--   liftIO $ dottyNode nn
--   liftIO . print . assocs =<< reversePostOrder nn
--   liftIO . print . IM.toList =<< mkIDomMap =<< idoms nn
--   liftIO $ dottyNode na

--   let wf = h3
--   liftIO $ dottyNode wf
--   liftIO . print =<< wellformed wf

  let pp = k3
  io $ dottyNode pp
  io $ pprint =<< toType pp
--   ops <- (n1 <? na)
--   case ops of
--     Nothing -> liftIO $ print "no instance"
--     Just ops' -> liftIO $ mapM_ print ops'
--   n1' <- copyNode n1
--   liftIO $ dottyNode n1
--   liftIO $ dottyNode n1'
--   liftIO $ print =<< mapM nodeId =<< graftables n1'
  return ()
 where
   new_bot = newNode Bot []
   new_fun a b = newNode (TyConNode Typ.funTyCon) [a,b]
   bind_flex a b = bindTo a (Just b) Flex
   bind_rigid a b = bindTo a (Just b) Rigid

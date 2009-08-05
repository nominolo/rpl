{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
module RPL.Typecheck.GrTy.Constraint where

import RPL.Typecheck.GrTy.Types
import RPL.Utils.Monads
import RPL.Utils.Misc

import qualified Data.IntSet as IS
import qualified Data.Map as M
import Control.Applicative
import Control.Monad ( foldM, when )
import Data.Maybe ( fromMaybe )
import Data.IORef

------------------------------------------------------------------------

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
  { cstore_root         :: Node
  , cstore_constraints  :: [ConstrEdge]
  , cstore_existentials :: [Node]
  } deriving (Eq, Show)

data ConstrType = MLF | ML


dfs_interior :: (Applicative m, MonadIO m {-, MonadError String m-} ) =>
                (Node -> m [Node])
             -> (Node -> m ())
             -> (Node -> m ())
             -> (Node -> m ())
             -> Node
             -> m ()
dfs_interior succs frontier pre post start_node = go IS.empty start_node >> return ()
  where
    go visited n = do
      nid <- nodeId n
      if (IS.member nid visited) then return visited 
       else do
        let visited' = IS.insert nid visited

        let frontier_node = frontier n >> return visited'
            normal_node = pre n *> (foldM go visited' =<< succs n) <* post n

        bnd <- getBinder n
        case bnd of
          Bound b -> do
            n' <- nodeId (bindBinder b)
            is_start_node <- nodesEqual n start_node
            if not is_start_node && not (IS.member n' visited') 
              then frontier_node
              else normal_node
          _otherwise -> normal_node

-- | Create a copy of a type scheme.  The inputs are the constaint store,
-- the constraint type to create (MLF instances look different than ML
-- instances) and the instantiation edge along which we are expanding.
--
-- Consider the classic instance-of operation.  For example, the type scheme
-- 
-- > forall a b. (a -> c) -> a -> b
--
-- where c is a free type variable.  This scheme can be instantiated by
-- dropping the foralls and substituting @a@ and @b@ with fresh variables:
--
-- > (a1 -> c) -> a1 -> b1
--
-- Note that @c@ is the same variable that was mentioned in the type scheme.
--
-- In our graph-based setting we don't have an explicit list of the
-- variables we can generalise over and which variables are free.  To find
-- this out we do two things.  We copy all nodes that are:
--
--  1. reachable from the source forall-node, and
--  2. that are transitively bound by the source forall node.
--
-- All nodes that are structurally reachable, but not transitively bound to
-- the source node must be considered monomorphic.  In order to preserve
-- well-formedness of the constraint trees the copied nodes will not
-- directly point to these nodes, but for each such node we create a new
-- variable node and add a unification edge connecting this new node and the
-- original tree.
--
-- TODO: example

-- Implementation notes:
--
-- We perform a top-down traversal starting from the forall-node and keep a
-- record of the nodes we have visited so far what their copies are called.
-- The interesting bit is the "transitively bound" part: a node is
-- transitively bound to our forall-node if it is bound at a node that we
-- have already visited (because of top-down direction).
--
expandForall :: (Applicative m, MonadIO m, MonadGen NodeId m, MonadError String m) => 
                ConstraintStore -> ConstrType -> ConstrEdge
             -> m (ConstraintStore, Node)
expandForall cstore constr_type edge = do
  let f_node = cedge_from edge
  let dest_node = cedge_to edge
  [f'_node] <- nodeChildren f_node
  copies <- liftIO $ newIORef M.empty
  new_constrs <- liftIO $ newIORef []
  dest_bndr <- binderNode dest_node

  let dest n = do nid <- nodeId n
                  fromMaybe n . M.lookup nid <$> (liftIO $ readIORef copies)

  let copied_node n = do nid <- nodeId n
                         M.lookup nid <$> (liftIO $ readIORef copies)

  let record_copy n n' = do nid <- nodeId n;
                            liftIO $ modifyIORef copies (M.insert nid n')

  let pre_mlf n = whenM (not <$> nodesEqual n f_node) $ do
        bnd <- getBinder n
        case bnd of
          Root -> error "expandForall.pre_mlf bad root"
          Bound b | n' <- bindBinder b, l <- bindLabel b -> do
            c_n <- newNode Bot []
            ifM (nodesEqual f'_node n)
              (do -- permissions reset case
                  bindFlexiblyTo c_n =<< copied_node n')
              (ifM (nodesEqual n' f_node)
                 (do -- binding reset case
                     b' <- copied_node f'_node
                     bindTo c_n b' l)
                 (do -- general case
                     b' <- copied_node n'
                     bindTo c_n b' l))
            record_copy n c_n

  let pre_ml n = whenM (not <$> nodesEqual n f_node) $ do
        bnd <- getBinder n
        case bnd of
          Root -> error "expandForall.pre_ml bad root"
          Bound b | bn <- bindBinder b, l <- bindLabel b -> do
            is_bound_at_f <- nodesEqual bn f_node
            when (l /= Flex || not is_bound_at_f) $
              throwError "MLFTypeMLFExpansion"
            c_n <- newNode Bot []
            c_n `bindFlexiblyTo` (Just bn)
            record_copy n c_n

  let post n = whenM (not <$> nodesEqual n f_node) $ do
        nsort <- nodeSort n
        children' <- mapM dest =<< nodeChildren n
        c_n <- newNode nsort children'
        Just c_n' <- copied_node n
        fuse c_n c_n' (Just c_n')

  let frontier n = do
        n' <- newNode Bot []
        bindFlexiblyTo n' (Just $ dest_bndr)
        let e = ConstrEdge { cedge_from = n', cedge_to = n
                           , cedge_type = Unify, cedge_origin = () }
        liftIO $ modifyIORef new_constrs (e:)
        record_copy n n'

  let pre n = case constr_type of
                MLF -> pre_mlf n
                ML -> pre_ml n
  
  record_copy f_node =<< binderNode dest_node
  dfs_interior nodeChildren frontier pre post f_node

  cs <- liftIO $ readIORef new_constrs
  cf' <- dest f'_node

  return ( cstore { cstore_existentials = cf' : cstore_existentials cstore
                  , cstore_constraints = cs ++ cstore_constraints cstore }
         , cf' )

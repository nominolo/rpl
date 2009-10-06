{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
module RPL.Typecheck.GrTy.Syntactic
  ( toType, fromType, mkCoercion )
where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Utils
import RPL.Type
import RPL.BuiltIn
import qualified RPL.Syntax as Syn
import RPL.Names
import RPL.Utils.Unique ( uniqueFromInt )
import RPL.Utils.Panic
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.List ( sortBy, find )
import Data.Ord ( comparing )
import Data.Maybe ( fromMaybe )
import RPL.Utils.Monads
import Control.Applicative
import Control.Exception ( assert )

-- | Translate a /syntactic/ type to a node.
--
-- The first result is the root of the type graph, the second is a list of
-- all existentially qualified vars.
-- 
-- TODO: This implicitly forall-qualifies unqualified vars.  We eventually
-- want to accept an TyVarEnv so we can refer to variables qualified above.
-- 
fromType :: (MonadGen NodeId m, Applicative m, MonadIO m) =>
            Syn.Type -> m (Node, [Node])
fromType user_type = do 
    (node, unbound) <- translate M.empty user_type
    mapM_ (\n -> bindTo n (Just node) Flex) unbound
    return (node, [])
  where
    translate env (Syn.TVar _ tv)
      | Just node <- M.lookup tv env = return (node, [])
      | otherwise = do 
          n <- newNode Bot []
          return (n, [n])
    translate env (Syn.TAll _ v ty) = do
      n <- newNode Bot []
      (n', free) <- translate (M.insert v n env) ty
      bindTo n (Just n') Flex
      return (n', free)
    translate env (Syn.TFun _ t1 t2) = do
      (n1, free1) <- translate env t1
      (n2, free2) <- translate env t2
      fn <- newNode (TyConNode funTyCon) [n1, n2]
      mapM (\n -> bindTo n (Just fn) Flex) [n1, n2]
      return (fn, free1 ++ free2)
          
    translate env ty =
      case Syn.viewTypeApp ty of
        (Syn.TCon _ tc_id, args) -> do
          case lookupTyCon tc_id of
            Just tycon 
             | length args == tyConArity tycon -> do
                 (ns, frees) <- translateList env args
                 tcn <- newNode (TyConNode tycon) ns
                 mapM_ (\n -> bindTo n (Just tcn) Flex) ns
                 return (tcn, frees)
             | otherwise -> error "Arity mismatch"  -- XXX: implement kind checker
            _ -> error "Unknown type constructor"   -- TODO: error message
        _ -> panic (text "Unknown application pattern")

    translateList _env [] = return ([], [])
    translateList env (t:ts) = do
      (n, free) <- translate env t
      (ns, frees) <- translateList env ts
      return (n:ns, free ++ frees)
    
    lookupTyCon n = M.lookup (idString n) initialTypeEnv
    initialTypeEnv =
      M.fromList [ (idString (tyConName tc), tc) 
                  | tc <- [intTyCon, charTyCon, maybeTyCon] ]

-- | Computes the coercion function for the given user type.
-- 
-- Coercion functions are used to implement type annotations.  Instead of
-- having a special rule for type annotations, we translate them to
-- applications of coercion functions:
-- 
-- > e :: t   ==>   c_t e
-- 
-- > \(x :: t) -> e  ==> \x -> let x = (x :: t) in e
-- 
-- A coercion is built by translating the type into a graph and then
-- creating a function type:
-- 
-- > c_t :: forall (a = t) (b > t). a -> b
-- 
-- Note the rigid binding of @a@.  This has the effect that if @t@ is
-- polymorphic, we /require/ the polymorphism in the argument and /allow/
-- polymorphism in the result.
-- 
-- Note that the two occurrences of @t@ are not shared.  We do, however, use
-- sharing for existentially bound variables:
-- 
-- > t = exists b. forall a. b -> (a -> a)
-- > c_t :: forall b 
-- >               (x = forall c. b -> (c -> c))
-- >               (y > forall e. b -> (e -> e)).
-- >          x -> y
-- 
mkCoercion :: (MonadGen NodeId m, Applicative m, MonadIO m) =>
              Syn.Type -> m Node
mkCoercion user_type = do
  (n, _existentials) <- fromType user_type
  n' <- copyNode n
  co <- newNode (TyConNode funTyCon) [n, n']
  bindTo n (Just co) Rigid  -- This is the key part.
  bindTo n' (Just co) Flex
  return co

toType :: (Applicative m, MonadIO m) => Node -> m Type
toType node = do
  rpo <- reversePostOrder node
  rpo_map <- nodeToPostOrder rpo
  bound_at <- rebind_to_root =<< inverseChildrenBinders node
  let go n = do
        n_id <- nodeId n
        let bound_at_n = 
              -- lowest first
              -- in increasing reverse post-order (i.e. post-order)
              map snd . sortBy (comparing fst) $
                [ (po, (l, n')) 
                  | (n'id,l,_,n') <- fromMaybe [] (IM.lookup n_id bound_at)
                  , let po = rpo_map IM.! n'id
                ]
        n_sort <- nodeSort n
        case n_sort of
          Bot -> do
            assert (bound_at_n == []) $ nodeIdToTyVar n_id
          TyConNode tc -> do
            bdrs <- binders n bound_at_n id
            cts <- substructs n =<< nodeChildren n
            return $ bdrs (tyConApp tc cts)

      binders _n0 [] !acc = return acc
      binders n0 ((l,n):lns) !acc = do
        n_id <- nodeId n
        inl <- can_inline bound_at n0 l n

        -- If we ca inline it we won't need to generate a binder, move on.
        if inl then binders n0 lns acc

         -- Otherwise, create a type variable and fill in 
         else do
          TyVar tv <- nodeIdToTyVar n_id
          t' <- go n
          let is_rigid = case l of Rigid -> True; _ -> False
          let ctxt = case t' of
                       TyVar tv' | tv == tv' -> BotCtxt
                       _ -> MLFCtxt is_rigid t'
          binders n0 lns (TyAll tv ctxt . acc)

      substructs _n0 [] = return []
      substructs n0 (n:ns) = do
        Bound b <- getBinder n
        inl <- can_inline bound_at n0 (bindLabel b) n
        t' <- if inl then go n
                     else nodeIdToTyVar =<< nodeId n
        (t':) <$> substructs n0 ns
          
  go node
 where
   --nodeIdToTyVar :: Int -> m Type
   nodeIdToTyVar n_id =
       let u = uniqueFromInt n_id in -- XXX:
       let x = Id u ("n" ++ show n_id) in
       return (TyVar $ mkTyVar x)

   can_inline bound_at t l n = do
     c_ids <- mapM nodeId =<< nodeChildren t
     n_id <- nodeId n
     mono <- monomorphic bound_at n
     if mono then return True else do
      let occs = length $ filter (n_id ==) c_ids
      if occs /= 1 then return False else do
       t_sort <- nodeSort t
       case t_sort of
         TyConNode tc -> do
           let Just (_,v) = find ((==n_id) . fst) (zip c_ids (variances tc))
           case (v,l) of
             (Covariant, Flex) -> return True
             (Contravariant, Rigid) -> return True
             _ -> return False
         _ -> return False

   monomorphic bound_at n = do
     n_sort <- nodeSort n
     case n_sort of
       Bot -> return False
       TyConNode _ -> do
         n_id <- nodeId n
         let bound_here =
               [ n' | (_,_,_,n') <- fromMaybe [] (IM.lookup n_id bound_at) ]
         and <$> mapM (monomorphic bound_at) bound_here

   -- We might have nodes that are bound above us at a generalisation
   -- node -- rebind those to our root ('node'), so that we can see them.
   --
   -- This does not include nodes that are generalised at a higher
   -- level, and are therefore monomorphic in this context.
   rebind_to_root bound_at = do
     gen_node_id <- nodeId =<< binderNode node
     n_id <- nodeId node
     let bound_at_gen = 
           [ x
           | Just bchildren <- [IM.lookup gen_node_id bound_at]
           , x@(n,_,_,_) <- bchildren 
           , n /= n_id ]
     return $ IM.insertWith (++) n_id bound_at_gen bound_at 

data Variance = Covariant | Contravariant deriving (Eq, Show)

variances :: TyCon -> [Variance]
variances tc
  | tc == funTyCon = [Contravariant, Covariant]
  | otherwise =
      -- XXX: probably wrong
      replicate (tyConArity tc) Covariant

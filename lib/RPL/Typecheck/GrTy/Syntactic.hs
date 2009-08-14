{-# LANGUAGE BangPatterns #-}
module RPL.Typecheck.GrTy.Syntactic ( toType, fromType ) where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Utils
import RPL.Type
import RPL.Names
import RPL.Utils.Unique ( uniqueFromInt )
import qualified Data.IntMap as IM
import Data.List ( sortBy, find )
import Data.Ord ( comparing )
import Data.Maybe ( fromMaybe )
import RPL.Utils.Monads
import Control.Applicative
import Control.Exception ( assert )


fromType :: (MonadIO m) => Type -> m Node
fromType = undefined

toType :: (Applicative m, MonadIO m) => Node -> m Type
toType node = do
  rpo <- reversePostOrder node
  rpo_map <- nodeToPostOrder rpo
  bound_at <- inverseChildrenBinders node
  let go n = do
        n_id <- nodeId n

        let bound_at_n = 
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
        if inl then binders n0 lns acc else do
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

data Variance = Covariant | Contravariant deriving (Eq, Show)

variances :: TyCon -> [Variance]
variances tc
  | tc == funTyCon = [Contravariant, Covariant]
  | otherwise =
      -- XXX: probably wrong
      replicate (tyConArity tc) Covariant

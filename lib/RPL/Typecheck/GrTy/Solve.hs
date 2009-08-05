{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
module RPL.Typecheck.GrTy.Solve where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Translate
import RPL.Typecheck.GrTy.Constraint
import RPL.Typecheck.GrTy.Unify ( unify )
import RPL.Utils.Monads
import RPL.Utils.Unique
import RPL.Utils.SrcLoc

import qualified RPL.Syntax as Syn
import qualified RPL.Names as Syn

import Control.Applicative
import Data.List ( find )

fastSolveOne :: (Applicative m, MonadIO m, MonadGen NodeId m, MonadError String m) => 
         Env -> ConstraintStore -> ConstrEdge -> m ConstraintStore
fastSolveOne env cs edge = do
  let n1 = cedge_from edge
      n2 = cedge_to edge
  (cs', n1', n2')
      <- case cedge_type edge of
           Unify -> return (cs, n1, n2)
           Inst -> do
             decrForallCount n1
             (cs', n') <- expandForall cs MLF edge
             --liftIO $ dottyConstraints cs' "expand_forall"
             return (cs', n', n2)
  unify env n1' n2'
  -- TODO: better error message
  return cs'

solve :: (Applicative m, MonadIO m, MonadGen NodeId m, MonadError String m) =>
         Env -> ConstraintStore -> m ConstraintStore
solve env cs_ = do
  let go _ cs | [] <- cstore_constraints cs = return cs
      go n cs | (e:es) <- cstore_constraints cs = do
        cs' <- fastSolveOne env (cs { cstore_constraints = es }) e
        --liftIO $ dottyConstraints cs' ("step " ++ show (n :: Int))
        go (n + 1) cs'
  go (0::Int) cs_

sv1 :: IO ()
sv1 = do
  let x = Syn.Id (uniqueFromInt 2) "x"
  let y = Syn.Id (uniqueFromInt 3) "y"
  let u = noSrcSpan
  let expr = Syn.ELam u (Syn.VarPat u x) $ -- (Syn.EVar u x)
              Syn.ELam u (Syn.VarPat u y) $ 
                Syn.EApp u (Syn.EVar u y) (Syn.EVar u x) 
-- Syn.EApp u
--                  (Syn.EApp u (Syn.EVar u x) (Syn.ELit u (Syn.IntLit 1)))
  r <- runGTM $ do 
         cs <- translate MLF [] expr
         liftIO $ do 
           --dumpConstraints cs
           dottyConstraints cs "initial"
         cs' <- solve [] cs
         liftIO $ do 
           --dumpConstraints cs'
           dottyConstraints cs' "final"
 
  return ()

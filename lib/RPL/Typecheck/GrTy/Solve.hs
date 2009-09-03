{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
module RPL.Typecheck.GrTy.Solve
  ( solve, SolveOpts(..), defaultSolveOpts,
    fastSolveOne )
where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Translate
import RPL.Typecheck.GrTy.Constraint
import RPL.Typecheck.GrTy.Unify ( unify )
import RPL.Utils.Monads

import Control.Applicative

data SolveOpts = SolveOpts
  { optDottyInitial :: Bool
    -- ^ Produce a dotty graph for the initial constraints.
  , optDottySteps :: Bool
    -- ^ Produce a dotty graph for each step.
  , optDottyResult :: Bool
    -- ^ Produce a dotty graph for the final result.
  , optConstrType :: ConstrType
    -- ^ Which type of constraint to generate for forall-expansion.
  }

defaultSolveOpts :: SolveOpts
defaultSolveOpts = SolveOpts
  { optDottyInitial = False
  , optDottySteps = False
  , optDottyResult = False
  , optConstrType = MLF
  }

fastSolveOne ::
       (Applicative m, MonadIO m, MonadGen NodeId m,
        MonadError String m) => 
       SolveOpts -> Env -> ConstraintStore -> ConstrEdge
    -> m ConstraintStore
fastSolveOne opts env cs edge = do
  let n1 = cedge_from edge
      n2 = cedge_to edge
  -- TODO: better error message
  case cedge_type edge of
    Unify -> do unify env n1 n2
                return cs
    Inst -> do decrForallCount n1
               (cs', n') <- expandForall cs (optConstrType opts) edge
               unify env n' n2
               return cs'

solve :: (Applicative m, MonadIO m, MonadGen NodeId m,
          MonadError String m) =>
         SolveOpts -> Env -> ConstraintStore -> m ConstraintStore
solve opts env cs_ = do
  when (optDottyInitial opts) $ io $ dottyConstraints cs_ "initial"
  let go _ cs | [] <- cstore_constraints cs = return cs
      go !n cs | (e:es) <- cstore_constraints cs = do
        cs' <- fastSolveOne opts env (cs { cstore_constraints = es }) e
        when (optDottySteps opts) $ do
          io $ dottyConstraints cs' ("step " ++ show (n :: Int))
        go (n + 1) cs'
  cs <- go (0::Int) cs_
  when (optDottyResult opts) $ io $ dottyConstraints cs "final"
  return cs

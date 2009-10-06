module RPL.Typecheck.Minimise where

import qualified Data.Map as M

-- | Find /a/ minimal unsatisfiable subset of the input constraints.
-- 
-- The particular kinds of constraints are mostly irrelevant.  They
-- should however commute (order does not matter) and the solver must
-- be a pure function.
-- 
-- Given @N@ input constraints, the solver function will be called at
-- most @N * (N / 2)@ (@sum [1..N]@) times.
-- 
-- Returns:
-- 
--  * @M.empty <=>@ the input constraints are satisfiable.
-- 
--  * @s <=>@ the input constraints are unsatisfiable and @s@ is a
--    minimal unsatisfiable set.  I.e., removing any element of @s@
--    makes it satisfiable.
-- 
minUnsat :: Ord k => 
    s  
    -- ^ Initial state of the solver.
 -> (s -> k -> c -> Either a s)
    -- ^ Solve a single constraint.  Either fail or return new state.
 -> M.Map k c
    -- ^ The input constraints.
 -> M.Map k c
minUnsat state0 run_one try_these = go state0 M.empty try_these
  where
    --
    -- INVARIANT:
    --   run_until_failure state0 min_approx == min_state
    --
    go min_state min_approx not_tried =

      case run_until_failure min_state not_tried of
        Right _ ->
          -- No failure.  The given constraints are satisfiable, thus
          -- there's no minimal unsatisfiable set.
          M.empty

        Left (last_tried_id, last_tried) ->
          -- The last constraint introduced a failure, hence it must
          -- be part of the minimal constraint set.
          case run_one min_state last_tried_id last_tried of
            Left _ ->
              -- Adding this one to our min_approx set fails, so
              -- this new set is minimal.  We're done!
              M.insert last_tried_id last_tried min_approx

            Right s' ->
              -- min_approx is still solvable, try the other
              -- constraints.
              go s' (M.insert last_tried_id last_tried min_approx)
                 (M.delete last_tried_id not_tried)
    
    -- Run the solver function on the input constraints until:
    --
    --  1) There are no more constraints left.  Return
    --     @Right final_state@.
    --
    --  2) A constraint fails.  Return @Left (k, failing_constraint)@
    --
    -- If the input constraints were:
    -- 
    -- > c_1, .., c_k, c_k+1, .., c_n
    -- 
    -- and the result is @Left c_k+1@, then the constraints @c_1, ..,
    -- c_k@ were consistent, but adding @c_k+1@ introduced an
    -- inconsistency.
    run_until_failure s not_tried =
      case M.minViewWithKey not_tried of
        Nothing -> Right s
        Just ((k, e), cs') ->
          case run_one s k e of
            Left _ -> Left (k, e)
            Right s' -> run_until_failure s' cs'


{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Typecheck.HMX.Unify 
  ( unifyVar, UnifyResult(..) )
where

import RPL.Typecheck.HMX.Core
import RPL.Typecheck.MultiEquation
import RPL.Utils.UnionFind as UF
import RPL.Utils.SrcLoc
import RPL.Utils.Monads
import RPL.Utils.Pretty
import RPL.Utils.Misc ( ifM )

import Control.Applicative

------------------------------------------------------------------------
-- | The result of unification; isomorphic to 'Maybe'.
data UnifyResult
    = Success Pool
    | CannotUnify SrcSpan (ArTerm Var) (ArTerm Var)

instance Pretty UnifyResult where
  ppr (Success _) = text "success"
  ppr (CannotUnify _ t1 t2) =
      text "Could not unify:" $+$
      nest 4 (ppr t1) $+$
      nest 4 (ppr t2)

type UnifyError = (SrcSpan, ArTerm Var, ArTerm Var)

newtype UnifyM a
  = UnifyM { unUnifyM :: StrictStateErrorT Pool UnifyError IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState Pool,
            MonadError UnifyError)

runUnifyM :: UnifyM a -> Pool -> IO UnifyResult
runUnifyM m pool = do
    r <- runStrictStateErrorT (unUnifyM m) pool
    case r of
      Right (_, pool')  -> return $ Success pool'
      Left (sp, t1, t2) -> return $ CannotUnify sp t1 t2

-- | Try to unify the two variables (and their associated structures).
--
-- This function does not calculate a substitution; instead, it
-- destructively modifies the equivalence classes of the involved variables.
-- Therefore, this function should be seen as unifying (two or more)
-- /equivalence classes/.
--
-- For example (@E1, E2, ...@ are equivalence classes before unification:
--
-- > E1: x1 = x2 = x3    E2: y1 = y2 = y3
-- > unifyVar s p x1 y1  ~~>  Success
-- > E1 = E2: x1 = x2 = x3 = y1 = y2 = y3
--
-- > E1: x1 = x2 = C y1    E2: y1 = y2    E3: z = C Int
-- > unifyVar s p x1 z   ~~>  Success
-- > E1: x1 = x2 = z = C y1    E2: y1 = y2 = Int
--
-- Two rigid variables cannot be unified:
--
-- > E1: x = C Int   E2: y = C Char
-- > unifyVar s p x y  ~~>  CannotUnify s Int Char
--
-- XXX: We need to be able to undo equivalence class updates in order to be
-- able to recover from unification failures.  A DiffArray-based Union/Find
-- could help.
--
-- INVARIANT: The rank of the resulting equivalence class will be the lower
-- of the two input classes' rank.
--
unifyVar :: SrcSpan  -- ^ Used as the error location.
         -> Pool     -- ^ TODO: Currently ignored (pass 'initialPool')
         -> Var -> Var
         -> IO UnifyResult
unifyVar pos0 pool0 var0_1 var0_2 = 
    runUnifyM (unify pos0 var0_1 var0_2) pool0
  where
    unify :: SrcSpan -> Var -> Var -> UnifyM ()
    unify pos var1 var2 =
      ifM (not <$> liftIO (UF.equivalent var1 var2))
        (unify' pos var1 var2)
        (return ())
 
    unify' :: SrcSpan -> Var -> Var -> UnifyM ()
    unify' pos var1 var2 = do
      desc1 <- liftIO $ descriptor var1
      desc2 <- liftIO $ descriptor var2

      -- Rigidness is contagious.
      let new_kind 
            | is_rigid desc1 = descKind desc1
            | is_rigid desc2 = descKind desc2
            | otherwise      = Flexible

      -- If both variables are named, prefer the one from the rigid thing.
      let new_name =
              case (descName desc1, descName desc2) of
                (Just n1, Just n2)
                  | n1 /= n2 ->
                      if is_rigid desc1 then Just n1 else
                       if is_rigid desc2 then Just n2
                        else Nothing
                  | otherwise ->
                      Just n1
                (Just n, _) -> Just n
                (_, Just n) -> Just n
                _ -> Nothing

      -- We keep the variable with the lower rank.
      let lower1 = descRank desc1 < descRank desc2

      -- merge1: Merge two multi-equations but keep the structure of the first
      -- merge2: Merge two multi-equations but keep the structure of the first
      let merge1 
           | lower1 = liftIO $ do
               UF.union var2 var1
               modifyDescriptor var1 $ \d -> d { descKind = new_kind
                                               , descName = new_name }
               return ()
           | otherwise = liftIO $ do
               UF.union var1 var2
               modifyDescriptor var2 $ \d -> d { descKind = new_kind
                                               , descName = new_name
                                               , descStruct = descStruct desc1 }
               return ()
      let merge2
           | lower1 = liftIO $ do
               UF.union var2 var1
               modifyDescriptor var1 $ \d -> d { descKind = new_kind
                                               , descName = new_name
                                               , descStruct = descStruct desc2 }
               return ()
           | otherwise = liftIO $ do
               UF.union var1 var2
               modifyDescriptor var2 $ \d -> d { descKind = new_kind
                                               , descName = new_name }
               return ()
      let merge | lower1    = merge1
                | otherwise = merge2
{-                 
      let fresh :: Maybe Structure -> UnifyM Var
          fresh s = do
            v <- liftIO $ UF.fresh (MkDescr
                      { descStruct = s
                      , descRank = descRank (if lower1 then desc1 else desc2)
                      , descMark = noMark
                      , descKind = new_kind
                      , descName = new_name
                      , descPos = noSrcSpan
                      , descVar = Nothing
                      })
            modify (register v)
            return v
-}
      case (descStruct desc1, descStruct desc2) of
        -- neither multi-equation contains a term
        (Nothing, Nothing) | is_flexible desc1 && is_flexible desc2 -> merge
        (Nothing, _)       | is_flexible desc1                      -> merge2
        (_, Nothing)       | is_flexible desc2                      -> merge1

        -- exactly one multi-equation contains a term; keep that one
        (Just (Var v), _) -> unify pos v var2
        (_, Just (Var v)) -> unify pos v var1

        -- it's forbidden to unify rigid type variables with a structure
        (Nothing, _) -> -- var1 is rigid
          throwError (pos, TVar var1, TVar var2)
        (_, Nothing) -> -- var2 is rigid
          throwError (pos, TVar var1, TVar var2)
        
        -- We're trying to unify two compound terms.
        (Just (App l1 r1), Just (App l2 r2)) -> do
          merge
          unify pos l1 l2 >> unify pos r1 r2

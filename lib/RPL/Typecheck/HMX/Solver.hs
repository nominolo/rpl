{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns #-}
module RPL.Typecheck.HMX.Solver where

import Prelude hiding ( foldr, mapM_, mapM )

import RPL.Typecheck.HMX.Constraint
import RPL.Typecheck.HMX.Unify
import RPL.Typecheck.MultiEquation ( Pool(..), Var, CrTerm, Descriptor(..),
                                     VarKind(..), noRank, noMark, outermost,
                                     Mark
                                   )
import qualified RPL.Typecheck.MultiEquation as ME
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Monads
import RPL.Utils.Pretty
import RPL.Utils.Panic ( expectJust )
import RPL.Utils.SrcLoc ( noSrcSpan )

import Data.List ( nub )
import Data.Maybe ( isJust )
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad ( when )
import qualified Data.Map as M
import Data.Array.IO
import System.IO.Unsafe ( unsafePerformIO )
import Control.Concurrent.MVar

------------------------------------------------------------------------

traceSolver :: MonadIO m => PDoc -> m ()
traceSolver _d = return () -- liftIO $ pprint d

newtype SolveM a
  = SolveM { unSolveM :: StrictStateErrorT Pool String IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState Pool,
            MonadError String)

runSolveM :: SolveM a -> Pool -> IO (Either String a)
runSolveM m p = fmap fst <$> runStrictStateErrorT (unSolveM m) p

data Env
  = EEmpty
  | EEnvFrame Env String Var

envToList :: Env -> [(String, Var)]
envToList env0 = go [] env0
  where go !acc EEmpty = acc
        go !acc (EEnvFrame e' name var) =
            go ((name, var) : acc) e'

solve :: TConstraint -> IO (Either String Env)
solve c = do
  let env = EEmpty
  let pool = ME.initialPool
  runSolveM (solve' env c) pool

solve' :: Env -> TConstraint -> SolveM Env
solve' env0 c0 = go env0 c0
  where
    go env c = 
      case c of
        CTrue _ -> return env

        Equals pos t1 t2 -> do
          v1 <- chop t1
          v2 <- chop t2
          unify_terms pos v1 v2
          return env

        And [] -> return env
        And cs -> do
          last <$> mapM (go env) cs

        -- Special case for @exists@
        Let [ForAll _ [] fqs c' _] (CTrue _) -> do
          mapM_ introduce fqs
          go env c'

        Let schemes c' -> do
          env' <- foldlM (\env' scheme' ->
                              concatEnv env' <$> solve_scheme env scheme')
                         env schemes
          go env' c'

        InstanceOf pos n term -> do
          s <- lookupEnv env n
          i <- instantiate s
          traceSolver $ text "instantiating" <+> ppr s <+> text "->" <+> ppr i
          t' <- chop term
          unify_terms pos i t'
          return env

    unify_terms pos v1 v2 = do
      traceSolver $ text "unifying" <+> ppr v1 <+> ppr v2
      pool <- get
      r <- liftIO $ unifyVar pos pool v1 v2
      case r of
        Success p' -> put p'
        CannotUnify _loc _t1 _t2 ->
            throwError $ pretty r

    solve_scheme env (ForAll _ [] [] c1 header) = do
      -- no need to generalise in this special case
      go env c1
      mapM (\(t,_) -> chop t) header

    solve_scheme env (ForAll _pos rqs fqs c1 header0) = do
      traceSolver $ text "Solving scheme: " <+> ppr rqs <+> ppr fqs
      pool <- get
      put $ ME.newPool pool
      mapM_ introduce rqs
      mapM_ introduce fqs
      --traceSolver $ ppr (rqs ++ fqs)
      header <- mapM (\(t,_) -> chop t) header0
      go env c1
      --get >>= traceSolver . ppr
      checkDistinctVars rqs
      pool' <- liftIO . generalise pool =<< get
      put pool'
      checkGenericVariables rqs
      return $ header

-- | Check that the variables are all distinct and have no associated
-- structure.
checkDistinctVars :: [Var] -> SolveM ()
checkDistinctVars vs = do
  vs' <- nub <$> forM vs (\v -> do 
           s <- liftIO (ME.varStructure v)
           if isJust s
             then throwError $ "Cannot generalise over structured variable: "
                               ++ pretty v
             else return v)
  if length vs' == length vs
   then return ()
   else throwError "Non-distinct variables"

-- | Check that the rank of all variables is 'ME.noRank'.
checkGenericVariables :: [Var] -> SolveM ()
checkGenericVariables vs =
  forM_ vs $ \v -> do
    d <- liftIO $ UF.descriptor v
    when (ME.descRank d /= ME.noRank) $ do
      throwError $ "Cannot generalise: " ++ pretty v

-- | Generalise over the variables in the young pool.
--
-- Our starting point is a type scheme of the form:
--
-- > forall x1 .. xn. exists z1 .. zm. [ E1 /\ .. /\ Ek ]
--
-- @E1@ through @Ek@ are solved multi-equations.  The young pool contains
-- the variables @x1, .., xn, z1, .. zn@, that is, all the variables that
-- are bound in the current scheme.  All variables referred to in @E1, ..,
-- Ek@ not in the young pool must be bound in the old pool.
--
-- Before generalising we try to minimise the number of young variables by
-- determining which ones are redundant.  We do this so that the type scheme
-- is minimal and therefore avoid duplicating work at instantiations of the
-- type scheme.
--
-- Redundant variables are:
--
--  1. All but one variable in a multi-equation, e.g.,
--
--     > x1 = x2 = x3 = y = ...
--
--     This is implemented by 'UF.redundant' which picks the oldest of the
--     variables in the pool (i.e., the variable with the lowest rank).
--
--  2. All variables that are substructures of variables from the old pool.
--     E.g., if @y@ is old in
--
--     > y = C x1 x2
--
--     then @x1@ and @x2@ are redundant, because they are determined by @y@.
--     Consequently, all substructures of @x1@ and @x2@ are now redundant as
--     well.
--
--  3. Variables where /all/ of the substructures are determined by the old
--     pool, e.g., if @y1@ and @y2@ are old in
--
--     > x = C y1 y2
--
--     then @x@ is redundant.  This in turn might render variables redundant
--     that contain @x@ as substructures.
--
-- After step (1) we can perform step (2) by traversing the young-variables
-- and descending into their sub-structures.  We then perform (3) on the way
-- back up.
--
-- All variables that were found not to be redundant are now generalised
-- over by setting their rank to 'ME.noRank'.
generalise :: Pool -- ^ The old pool.
           -> Pool -- ^ The young pool.
           -> IO Pool -- ^ The possibly modified old pool.
generalise old_pool young_pool = do
  --traceSolver $ ppr old_pool
  let young_rank = ME.poolRank young_pool

  -- Remove all redundant variables from each multi-equation (Rule 1) and
  -- collect all remaining variables grouped by their rank.
  sorted <- newArray (0, young_rank) [] :: IO (IOArray ME.IntRank [Var])
  let young_vars = ME.poolVars young_pool -- XXX: filter some more
  --traceSolver $ text "youngs:" <+> ppr young_vars
  young <- freshMark
  forM_ young_vars $ \v -> do
    r <- ME.descRank <$> UF.descriptor v
    UF.modifyDescriptor v (\d -> d{ ME.descMark = young })
    writeArray sorted r . (v:) =<< readArray sorted r

  visited <- freshMark
  
  -- Beginning at each variable in @sorted@ we follow its descendants and
  -- make sure that their ranks are less or equal to the parent's rank (Rule
  -- 2).
  --
  -- On the way back up we then ensure that the rank of each variable is the
  -- maximum of the ranks of its substructures (Rule 3).
  --
  -- We start with the lowest ranks first since that allows us to work with
  -- cyclic structures (according to Pottier and Rémy).
  forM_ [0 .. young_rank] $ \k -> do

    let walk var = do
          descr <- UF.descriptor var
          case () of
           _ | ME.descMark descr == young -> do
             -- The variable is young and unvisited.  Mark it as visited
             -- /first/, then traverse into its children.  On the way back
             -- up set the rank if needed.
             modVar var (\d -> d{ ME.descMark = visited })
             case ME.descStruct descr of
               Nothing -> do
                 modVar var (\d -> d{ ME.descRank = k })
                 return k
               Just term -> do
                 rank' <- foldlM (\acc child -> max acc <$> walk child)
                                 ME.outermost term
                 modVar var (\d -> d{ ME.descRank = rank' })
                 return rank'
           _ | not (ME.descMark descr == visited) -> do
             -- the variable is neither young nor visited, thus it must be
             -- an old variable.  Do not traverse into its children, but
             -- update its rank if needed.
             modVar var (\d -> d{ ME.descMark = visited })
             if k < ME.descRank descr then
                do modVar var (\d -> d{ ME.descRank = k })
                   return k
               else
                 return $ ME.descRank descr
           _ ->
             -- it's young and visited => we're done.
             return $ ME.descRank descr
    vs <- readArray sorted k
    --traceSolver $ text "walking" <+> ppr k <+> ppr vs
    mapM_ walk vs
  
  -- All the young variables that have a rank @< young_rank@ are definitely
  -- old, so we can add them to the old pool straight away.
  old_youngs <- Prelude.concat . safeInit <$> getElems sorted
  let old_pool' = ME.registerVars old_youngs old_pool

  youngs <- readArray sorted young_rank
  
  -- Now traverse all the young vars and filter out the ones that have been
  -- found redundant (according to rules 2 and 3) and put them into the old
  -- pool.  We quantify over the remaining vars by setting their rank to
  -- 'ME.noRank' and making them rigid.
  old_youngs' <-
     foldlM (\olds var -> do
               descr <- descriptor var 
               if ME.descRank descr < young_rank
                then do 
                  --traceSolver $ ppr var <+> text "is old, (rank" <+> 
                  --              ppr (ME.descRank descr) <+> char ')'
                  return (var : olds)
                else do
                  --traceSolver $ text "generalising over" <+> ppr var
                  modVar var 
                        (\d -> d{ ME.descRank = ME.noRank
                                , ME.descKind = 
                                    if ME.descKind d == ME.Flexible
                                     then ME.Rigid
                                     else ME.descKind d })
                  return olds)
            []
            youngs
  return $ ME.registerVars old_youngs' old_pool'

-- | Instantiate the type scheme referred to by the input variable.
--
-- This is done by copying each quantified variable once (i.e., all the
-- variables reachable from the argument that have rank 'ME.noRank'.)  The
-- copied variables will be nameless and 'Flexible'.
instantiate :: Var -> SolveM Var
instantiate var = do
  -- To make sure every variable is only copied once, we use the 'descMark'
  -- field and save a pointer to the new copy in 'descVar'.  That is, the
  -- invariant is @descMark d == m ==> isJust (descVar d)@ and the rank of
  -- the variable pointed to by @descVar@ is the same as the current pool.
  --
  -- TODO: Compare efficiency to non-copying implementation.
  m <- liftIO $ freshMark
  var' <- copy m var
  restore m var
  return var'
 where
   -- Recursively copies the substructures.
   copy :: ME.Mark -> Var -> SolveM Var
   copy m v = do
     d <- liftIO $ UF.descriptor v
     case () of
      _ | ME.descMark d == m ->
        -- The variable has already been copied, descVar points to the copy.
        get_copied_var d

      _ | ME.descRank d /= ME.noRank || ME.descKind d == Constant -> do
        -- We don't need to copy monomorphic variables or constants
        return v

      _ | otherwise -> do
        v' <- liftIO $ ME.variable Flexible (case descKind d of
                                               Rigid -> Nothing
                                               _ -> descName d)
                                   Nothing noSrcSpan
        introduce v'
        mark_copied v m v'
        case descStruct d of
          Nothing -> return v'
          Just term -> do
            term' <- mapM (copy m) term
            modVar v' (\de -> de{ descStruct = Just term' })
            return v'

   mark_copied v m v' =
     modVar v (\d -> d{ descMark = m
                      , descVar = Just v' })
   get_copied_var d =                                                       
     return $ expectJust "instantiate: copy marked var" (ME.descVar d)

   -- Remove the marks.  Resetting the 'descVar' fields is mostly to avoid
   -- space leaks.  We don't strictly need to remove the mark, since the
   -- next instantiation will use a different mark.
   restore m v = do
     d <- descriptor v
     when (descMark d == m) $ do
       modVar v (\d' -> d'{ descVar = Nothing
                          , descMark = noMark })
       case descStruct d of
         Nothing -> return ()
         Just term -> mapM_ (restore m) term

-- | Safe version of 'init'.  
safeInit :: [a] -> [a]
safeInit [] = []
safeInit xs = init xs

-- XXX: ugh, ugly global var!  At least it's thread safe.
markVar :: MVar Mark
markVar = unsafePerformIO $ newMVar 0

freshMark :: IO Mark
freshMark = modifyMVar markVar (\x -> return (x + 1, x))

modVar :: MonadIO m => Var -> (Descriptor -> Descriptor) -> m ()
modVar v f = liftIO $ UF.modifyDescriptor v f

descriptor :: MonadIO m => Var -> m Descriptor
descriptor v = liftIO $ UF.descriptor v

concatEnv :: Env -> M.Map String Var -> Env
concatEnv env0 m =
  M.foldWithKey (\name var env -> EEnvFrame env name var) env0 m
     
chop :: CrTerm -> SolveM Var
chop t = do
  --traceSolver $ text "chopping" <+> ppr t
  pool <- get
  (pool', var) <- liftIO $ ME.chop pool t
  put pool'
  --traceSolver $ text "chopping done" <+> ppr var
  return var

introduce :: Var -> SolveM ()
introduce v = do
  pool <- get
  put =<< liftIO (ME.introduce v pool)

lookupEnv :: Env -> SchemeName -> SolveM Var
lookupEnv (EEnvFrame env name' scheme_var) n@(SName name)
  | name == name' = return scheme_var
  | otherwise = lookupEnv env n
lookupEnv EEmpty n =
    throwError $ "Unbound identifier:" ++ pretty n

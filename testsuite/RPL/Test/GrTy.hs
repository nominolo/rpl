{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Test.GrTy where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Unify
import RPL.Typecheck.GrTy.Translate
import RPL.Typecheck.GrTy.Constraint
import RPL.Typecheck.GrTy.TestUtils

import qualified RPL.Type as Typ
import qualified RPL.BuiltIn as Typ
import RPL.Utils.Monads

import Control.Applicative
import Control.Monad ( forM_, foldM )
import Data.Supply
import Data.Maybe ( isJust )
import Test.HUnit hiding ( Node )
import Test.QuickCheck
import Test.QuickCheck.Monadic as QC
import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import qualified Data.IntMap as IM
-- import qualified Data.Set as S
import System.IO.Unsafe ( unsafePerformIO )
--import System.Random

instance Monad m => Applicative (PropertyM m) where
  pure = return
  fm <*> xm = do f <- fm
                 x <- xm
                 return (f x)

instance MonadIO m => MonadIO (PropertyM m) where
  liftIO = run . liftIO

instance MonadGen s m => MonadGen s (PropertyM m) where
  getSupply = run getSupply
  setSupply s = run (setSupply s)

tests :: [F.Test]
tests = [ testGroup "graphic types" $
  [ testGroup "basic" $
    [ testCase "new_node" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        b <- nodesEqual n1 n2
        liftIO $ not b @? "New nodes must be distinct"
    , testCase "congruent/1" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        b <- congruent n1 n2
        liftIO $ b @? "Bare bottom nodes are congruent"
    , testCase "congruent/2" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode (TyConNode Typ.typeInt) []
        b <- congruent n1 n2
        liftIO $ not b @? "Int and variable are not congruent"
    , testCase "congruent/3" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        n3 <- newNode (TyConNode Typ.funTyCon) [n1, n2]
        n4 <- newNode Bot []
        n5 <- newNode Bot []
        n6 <- newNode (TyConNode Typ.funTyCon) [n4, n5]
        b <- congruent n3 n6
        liftIO $ b @? "Isomorphic types should be congruent"
    , testCase "congruent/4" $ runM $ do
        n1 <- newNode Bot []
        n3 <- newNode (TyConNode Typ.funTyCon) [n1, n1]
        n4 <- newNode Bot []
        n5 <- newNode Bot []
        n6 <- newNode (TyConNode Typ.funTyCon) [n4, n5]
        b <- congruent n3 n6
        liftIO $ not b @? "Too much sharing on the left"
    , testCase "congruent/5" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        n3 <- newNode (TyConNode Typ.funTyCon) [n1, n2]
        n4 <- newNode Bot []
        n6 <- newNode (TyConNode Typ.funTyCon) [n4, n4]
        b <- congruent n3 n6
        liftIO $ not b @? "Too much sharing on the right"
    , testCase "congruent/6" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        n3 <- newNode (TyConNode Typ.funTyCon) [n1, n2]
        n4 <- newNode Bot []
        n6 <- newNode (TyConNode Typ.funTyCon) [n1, n4]
        b <- congruent n3 n6
        liftIO $ b @? "Shared node is congruent"
    , testCase "congruent/7" $ runM $ do
        -- This holds according to the definition (perhaps strangely)
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        n3 <- newNode (TyConNode Typ.funTyCon) [n1, n2]
        n4 <- newNode Bot []
        n6 <- newNode (TyConNode Typ.funTyCon) [n4, n1]
        b <- congruent n3 n6
        liftIO $ b @? "Shared node is congruent"
 
    ]

  -- (forAll $ \a b -> a .->. (forAll $ \c -> c .->. b))

  , testGroup "unify" $
    [ testCase "simple" $ runM $ do
        n1 <- newNode Bot []
        n2 <- newNode Bot []
        n3 <- newNode (TyConNode Typ.funTyCon) [n1, n2]
        forM_ [n1,n2] $ (`bindFlexiblyTo` Just n3)
        unify [] n1 n2
        b <- nodesEqual n1 n2
        liftIO $ b @? "New nodes must be equal after unification"
    , testProperty "does not crash" $ prop_no_crash
    , testProperty "prop_copy" $ prop_copy
    , testProperty "graft/1" $ prop_graft1
    , testProperty "graft/2" $ prop_graft2
    , testProperty "prop_unif_inst" $ prop_unif_inst
    ]

    -- unification properties:
    -- 
    -- - the unified type is an instance of the input type
    -- 
    -- - it's term shape structure is the same as term-unification
    -- 
    -- - take a type t with two nodes n1, n2, apply a random sequence of
    --   instance operations on n1 to obtain type t1, do the same to for n2
    --   to obtain type t2.  unify(t2, n1, n2) must be an instance of t and
    --   the type at n1 (==n2) in the result must be a subtype of both n1 in
    --   t1 and n2 in t2.

  ] ]

prop_no_crash :: Property
prop_no_crash = monadicIO $
  forAllM (arbitrary :: Gen GrT) $ \grty -> do
    run $ runM $ do
      n <- fromGrT grty
      cs <- nodeChildren n
      case cs of
        [] -> return True
        [n1,n2] -> do
           (unify [] n1 n2 >> return True)
           `catchError` (\e -> return True)
    >>= QC.assert

    

prop_copy :: Property
prop_copy = monadicM $ 
  forAllM (arbitrary :: Gen GrT) $ \grty -> do
    n <- run $ fromGrT grty
    wf <- wellformed n
    pre wf
    n' <- run $ copyNode n
    ok <- locallyCongruent n n'
    if ok then QC.assert ok else do
      liftIO $ dottyNode n
      liftIO $ dottyNode n'
      QC.assert ok

prop_graft1 :: Property
prop_graft1 = monadicM $ 
  forAllM (arbitrary :: Gen GrT) $ \grty -> do
    n <- run $ fromGrT grty
    gs <- run $ graftables n
    pre (not (null gs))
    forAllM (elements gs) $ \g -> do
      ok <- graft1 g Typ.funTyCon
      QC.assert ok

prop_graft2 :: Property
prop_graft2 = monadicM $ 
  forAllM (arbitrary :: Gen GrT) $ \grty -> do
    n <- run $ fromGrT grty
    n0 <- run $ copyNode n
    gs <- run $ graftables n
    wf <- run $ wellformed n
    pre (not (null gs) && wf)
    --liftIO $ print (gs, n, n0)
    forAllM (elements gs) $ \g -> do
      ok <- run $ graft1 g Typ.funTyCon
      n' <- run $ copyNode n
      QC.assert ok
      --liftIO $ print (gs, n0, n)
      mb_ops <- run $ n0 <? n
      case mb_ops of
        Just ops -> do
          if length ops == 1 then QC.assert True else do
            liftIO $ dottyNode n0
            liftIO $ dottyNode n'
            liftIO $ dottyNode n
            liftIO $ print (">>",ops)
            QC.assert False
        Nothing -> do
          liftIO $ print "no instance"
          QC.assert False

prop_unif_inst :: Property
prop_unif_inst = monadicM $
  forAllM (arbitrary :: Gen GrT) $ \grty -> do
    n <- run $ fromGrT grty
    wf <- run $ wellformed n
    cs <- run $ nodeChildren n
    pre (not (null cs) && wf)
    case cs of
      [n1,n2] -> do
        n0 <- run $ copyNode n
        ok <- run $ (do unify [] n1 n2
                        is_inst <- n0 <? n
                        return (isJust is_inst) )
                    `catchError` (\e -> return True)
        QC.assert ok

monadicM :: PropertyM M a -> Property
monadicM = monadic (unsafePerformIO . runM)

--  instance operation  | generalisation operation
-- -------------------------------------------------------------------------
--  graft               | un-graft (replace a closed subtree by a variable)
--  merge               | split a node in two
--  raise               | lower a binding edge
--  weaken              | strengthen (replace rigid edge by flexible edge)


-- Instance checking: (generate an audit trail of instance operations?)
-- 
-- a <- b < c <- d  iff a < c and b < d
-- var < t          if binding structure is ok
-- 

-- Test for failure of unification: how?

-- Instance checking: generate types and check whether they are an instance
-- of another type.

type NId = Int
type NBinder = Int
type NChildren = [NId]
type NNode = (NId, NodeSort, NBinder, NChildren)

-- A pure 
data GrT = GrT NId (IM.IntMap NNode) deriving (Show)

instance Arbitrary GrT where
  arbitrary = arbGrT

arbGrT :: Gen GrT
arbGrT = do 
    (root_id, all_nodes, _, _) <- go 1 [] [] IM.empty 
    return (GrT root_id all_nodes)
  where
    go :: NId -> [NId] -> [NNode] -> IM.IntMap NNode 
       -> Gen (NId, IM.IntMap NNode, NId, [NNode])
    go next_id parents vars all_nodes = do
      -- a node without any children
      let end_node :: Gen (NId, IM.IntMap NNode, NId, [NNode])
          end_node = frequency $ 
            [-- node is a variable that is already used elsewhere
             (if null vars then 0 else 2,
                 do (v_id,_,_,_) <- elements vars
                    return (v_id, all_nodes, next_id, vars))
            ,-- node is monomorphic
             (1, do nsort <- elements [Typ.typeInt, Typ.typeChar]
                    let bdr = if null parents then 0 else head parents
                    let new_node = (next_id, TyConNode nsort, bdr, [])
                    let all_nodes' = IM.insert next_id new_node all_nodes
                    return (next_id, all_nodes', next_id+1, vars))
            ,-- create a fresh variable, flexibly bound at the parent node
             -- This ensures well-formedness
             (1, do let bdr = if null parents then 0 else head parents
                    let vnode = (next_id, Bot, bdr, [])
                    return (next_id,
                            IM.insert next_id vnode all_nodes,
                            next_id+1, vnode:vars))
            ]
      sized $ \n -> do
        if n <= 1 then end_node else
          frequency $ 
            [(1, end_node)
            ,(3, -- we only generate function nodes, for now
                 do (c1, an', next_id', vars') 
                        <- resize (n `div` 2) $ 
                            go (next_id + 1) (next_id:parents) vars all_nodes
                    (c2, an'', next_id'', vars'')
                        <- resize (n `div` 2) $ go next_id' (next_id:parents) vars' an'
                    let bdr = if null parents then 0 else head parents
                    let new_node = (next_id, TyConNode Typ.funTyCon, bdr, [c1,c2])
                    let all_nodes' = IM.insert next_id new_node an''
                    return ( next_id
                           , all_nodes'
                           , next_id''
                           , vars''))]

fromGrT :: (Applicative m, MonadIO m, MonadGen NodeId m) => 
           GrT -> m Node
fromGrT (GrT root nodes) = fst <$> mkNode IM.empty root
 where
   mkNode known gt_id | Just n <- IM.lookup gt_id known =
     return (n, known)
   mkNode known gt_id = do
     let Just (_, nsort, _bdr, cs) = IM.lookup gt_id nodes
     (ns, known') <- mkNodes known cs
     n <- newNode nsort ns
     mapM_ (`bindFlexiblyTo` Just n) ns
     return (n, IM.insert gt_id n known')

   mkNodes known [] = return ([], known)
   mkNodes known (g:gs) = do
     (n, known') <- mkNode known g
     (ns, known'') <- mkNodes known' gs
     return (n:ns, known'')
       

__ :: a
__ = undefined

t2 :: IO ()
t2 = runM $ do 
       ts <- liftIO $ sample' (arbitrary :: Gen GrT)
       ns <- mapM fromGrT ts
       forM_ ns $ \n -> do
          liftIO $ dumpConstraints (ConstraintStore n [] [])
          cs <- nodeChildren n
          case cs of
            [] -> return ()
            [n1,n2] -> do
                n1id <- nodeId n1; n2id <- nodeId n2
                liftIO $ print ("unifying", n1id, n2id)
                (do unify [] n1 n2
                    liftIO $ dumpConstraints (ConstraintStore n [] []))
                 `catchError` (\e -> liftIO $ print e)
        

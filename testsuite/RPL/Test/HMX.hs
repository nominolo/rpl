module RPL.Test.HMX where

import RPL.Typecheck.HMX
import RPL.Typecheck.HMX.Unify
import RPL.Typecheck.HMX.Solver
import RPL.Typecheck.MultiEquation hiding ( chop )
import qualified RPL.Typecheck.MultiEquation as ME
import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Pretty
import RPL.Utils.SrcLoc

import Test.HUnit
import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit
import qualified Data.Map as M
import qualified Data.Set as S

tests :: [F.Test]
tests = [ testGroup "HM(X)" $
  [ testGroup "unify" $
    [ testCase "fresh multi-equ" $ do
        a <- mkVar Flexible "a"
        b <- mkVar Flexible "b"
        equivalent a b >>= (@? "Variables must be distinct") . not
    , testCase "unify fresh" $ do
        a <- mkVar Flexible "a"
        b <- mkVar Flexible "b"
        unifyVar noSrcSpan initialPool a b >>= assertUnifies True
    , testCase "unify rigid" $ do
        a <- mkVar Rigid "a"
        b <- mkVar Rigid "b"
        unifyVar noSrcSpan initialPool a b >>= assertUnifies False
    , testCase "unify rigid/flexible" $ do
        a <- mkVar Flexible "a"
        b <- mkVar Rigid "b"
        unifyVar noSrcSpan initialPool a b >>= assertUnifies True
        isRigid a >>= assertBool "a must be rigid"
    ]
  , testGroup "solve" $
    [ testCase "true" $ do
        r <- solve true
        fmap envToList r @?= Right []
    , testCase "equiv/1" $ do
        k <- mkVar Constant "Int"
        a <- mkVar Flexible "a"
        r <- solve (TVar k =?= TVar a)
        fmap envToList r @?= Right []
        equivalent a k >>= (@? "Variables must be unified")
    , testCase "equiv/and" $ do
        k <- mkVar Constant "Int"
        a <- mkVar Flexible "a"
        b <- mkVar Flexible "b"
        r <- solve (TVar k =?= TVar a /\ TVar k =?= TVar b)
        fmap envToList r @?= Right []
        equivalent a b >>= (@? "Variables must be unified")
    , testCase "equiv/exists" $ do
        k <- mkVar Constant "Int"
        r <- solve =<< (exists $ \x -> return (x =?= TVar k))
        fmap envToList r @?= Right []
    , testCase "equiv/forall/1" $ do
        x <- mkVar Rigid "x"
        y <- mkVar Flexible "y"
        r <- solve $ Let [ForAll noSrcSpan [x] [y] (TVar x =?= TVar y)
                                    (M.fromList [("foo", (TVar x, noSrcSpan))])] (CTrue noSrcSpan)
        fmap envToList r @?= Right [("foo",x)]
    , testCase "equiv/forall/2" $ do
        x <- mkVar Rigid "x"
        y <- mkVar Flexible "y"
        r <- normaliseEnv =<< solve 
               (Let [ForAll noSrcSpan [x] [y] (TVar x =?= TVar y)
                             (M.fromList [("foo", (TVar y, noSrcSpan))])]
                         (CTrue noSrcSpan))
        r @?= Right [("foo",x)]
    , testCase "equiv/forall/3" $ do
        k <- mkVar Constant "C"
        x <- mkVar Rigid "x"
        r <- normaliseEnv =<< solve
               (forAll [k]
               (Let [ForAll noSrcSpan [x] [] true
                       (M.fromList [("foo", (TTerm (TVar k `App` TVar x), noSrcSpan))])]
                 true))
        r @?= Right []
    , testCase "instance/1" $ do
        k <- mkVar Constant "C"
        i <- mkVar Constant "I"
        x <- mkVar Rigid "x"
        let c = (forAll [k,i]
                (Let [ForAll noSrcSpan [x] [] true
                       (M.fromList [("foo", (TTerm (TVar k `App` TVar x), noSrcSpan))])]
                 (SName "foo" <? (TTerm (TVar k `App` TVar i)))))
        r <- normaliseEnv =<< solve c
        r @?= Right []
    , testCase "instance/2" $ do
        k <- mkVar Constant "C"
        i <- mkVar Constant "I"
        x <- mkVar Rigid "x"
        let c = (forAll [k,i]
                (Let [ForAll noSrcSpan [x] [] true
                       (M.fromList [("foo", (TTerm (TVar k `App` TVar x), noSrcSpan))])]
                 (And [(SName "foo" <? (TTerm (TVar k `App` TVar i))),
                      (SName "foo" <? (TTerm (TVar k `App` TVar k)))])))
        r <- normaliseEnv =<< solve c
        r @?= Right []
   ]
  ] ]

normaliseEnv :: Either String Env -> IO (Either String [(String, Var)])
normaliseEnv (Right e) =
    Right `fmap` mapM (\(n,v) -> do v' <- UF.repr v; return (n, v')) (envToList e)
normaliseEnv (Left err) = return $ Left err


assertUnifies :: Bool -> UnifyResult -> Assertion
assertUnifies expect_success r =
  case r of
    Success _ | not expect_success ->
        assertFailure "Unexpected unification success."
    f@(CannotUnify _ _ _) | expect_success ->
        assertFailure $ pretty f
    _ -> return ()

t1 = do [a,b,c,d,e,f,g,h] 
            <- sequence [ variable Flexible (Just $ TName x) Nothing noSrcSpan
                            | x <- ["a","b","c","d","e","f","g","h"]]
        pprint [a,b,c,d]
        r <- unifyVar noSrcSpan initialPool a b
        pprint r
        pprint [a,b,c,d]

        k_C <- variable Constant (Just $ TName "C") Nothing noSrcSpan
        c' <- variable Flexible (Just $ TName "C") (Just (App k_C k_C)) noSrcSpan
        d' <- variable Flexible (Just $ TName "C") (Just (App k_C f)) noSrcSpan
        pprint [k_C, c', d', e, f]

        pprint =<< unifyVar noSrcSpan initialPool c' d'
        pprint [c', d', e, f]
        
        let term = TTerm (App (TVar k_C) (TTerm (App (TVar k_C) (TVar h))))
        let pool = initialPool
        (pool'@(MkPool r vs), v) <- ME.chop pool term
        pprint (v, r, vs)
--        pprint =<< equivalent 


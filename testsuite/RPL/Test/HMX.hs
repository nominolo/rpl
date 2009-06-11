module RPL.Test.HMX where

import RPL.Typecheck.HMX
import RPL.Typecheck.HMX.Unify
import RPL.Typecheck.MultiEquation
import RPL.Utils.Pretty
import RPL.Utils.SrcLoc

import Test.HUnit
import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit

tests :: [F.Test]
tests = [ testGroup "HM(X)" $
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
  ] ]

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
        (pool'@(MkPool r vs), v) <- chop pool term
        pprint (v, r, vs)
--        pprint =<< equivalent 

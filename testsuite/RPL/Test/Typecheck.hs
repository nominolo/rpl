-- | Testing the type checker.  (soundness only, not completeness--how?)
--
-- Basic idea: generate terms of which we know the type, then run the type
-- checker on the term and check whether they are the same (or compatible).
-- 
module RPL.Test.Typecheck where

--import RPL.Names
import RPL.Type
import RPL.Syntax hiding ( Type(..) )
import RPL.BuiltIn
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
import RPL.Typecheck.Monad
import RPL.Typecheck.Utils

import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit
import Test.HUnit
import Test.QuickCheck
import Data.Maybe ( isJust, isNothing )
import Debug.Trace

tests :: [F.Test]
tests = [ testGroup "typecheck" $
  [ testCase "freshTyVar" $ runTcM' $
      do [a,b] <- mapM freshTyVar ["a", "b"]
         return (a == b @?= False)
  , testCase "mkFun/1" $ runTcM' $ do
      [a,b,c] <- mapM freshTyVar ["a", "b", "c"]
      return $ (a .->. b .->. c) @?= (a .->. (b .->. c))
  , testCase "mkFun/2" $ runTcM' $ do
      [a,b,c] <- mapM freshTyVar ["a", "b", "c"]
      return $ mkFun [a, b, c] @?= (a .->. (b .->. c))
  , testCase "TyApp assoc" $ runTcM' $ do
      [a,b,c] <- mapM freshTyVar ["a", "b", "c"]
      return $ a @@ b @@ c @?= (a @@ b) @@ c

  , testCase "instanceOf/1" $ runTcM' $ do
      [a,b] <- mapM freshTyVar ["a", "b"]
      let s1 = mkForall [a] [] (typeMaybe @@ a .->. typeMaybe @@ a)
          s2 = mkForall [b] [] (b .->. b)
      instanceOfCheck True s1 s2
  , testCase "instanceOf/2" $ runTcM' $ do
      [a,b] <- mapM freshTyVar ["a", "b"]
      let s1 = mkForall [a] [] ((a .->. a) .->. (a .->. a))
          s2 = mkForall [b] [] (b .->. b)
      instanceOfCheck True s1 s2
  , testCase "instanceOf/3" $ runTcM' $ do
      [a,b] <- mapM freshTyVar ["a", "b"]
      let s1 = mkForall [a] [] ((a .->. a) .->. (a .->. a))
          s2 = mkForall [b] [] (b .->. b)
      instanceOfCheck False s2 s1
  , testCase "instanceOf/4" $ runTcM' $ do
      [a,b] <- mapM freshTyVar ["a", "b"]
      let s1 = mkForall [a] [] ((a .->. a) .->. a)
          s2 = mkForall [b] [] (b .->. b)
      instanceOfCheck False s1 s2
  , testCase "instanceOf/5" $ runTcM' $ do
      [a,b] <- mapM freshTyVar ["a", "b"]
      let s1 = mkForall [a] [] (typeInt .->. a)
          s2 = mkForall [b] [] (b .->. b)
      instanceOfCheck False s1 s2
  ]]

instanceOfCheck :: Bool -> TypeScheme -> TypeScheme -> TcM Assertion
instanceOfCheck exp s1 s2 = do
    b <- s1 `isInstanceOf` s2
    return $ exp == b @? msg
  where msg = pretty s1 ++ (if exp then " <= " else " !<= ") ++ pretty s2

runTcM' :: TcM Assertion -> Assertion
runTcM' m =
  case runTcM m of
    Left err -> assertFailure $ "Typechecking failed with: " ++ show err
    Right a  -> a

withTyVars :: ([TyVar] -> Assertion) -> Assertion
withTyVars f = runTcM' $ f <$> mapM freshTyVar simpleNames
  

{-
-- | Check whether the first argument is an instance of the second one.
--
-- Automatically calculates a substitution.  The rules are
--
-- @
--                      s1 < [a := t](s2)
-- ------- SUB-MONO    ------------------- SUB-INST
--  t < t               s1 < forall a. s2
--
--  s1 < s2    a not in ftv(s2)
-- ---------------------------- SUB-SKOL
--      forall a. s1 < s2
-- @
--
-- TODO: Currently this ignores constraints.  Do we need some form of
-- weakening or strengthening?  Do we want both notions, i.e., instantiation
-- including and excluding constraints?
isInstanceOf :: TypeScheme -> TypeScheme -> Bool
isInstanceOf ts1 ts2 = isJust $ isInstanceOf' ts1 ts2

isInstanceOf' :: TypeScheme -> TypeScheme -> Maybe TySubst
isInstanceOf' (ForAll tvs1 _ t1_0) (ForAll tvs2 _ t2_0) =
--    check emptyTySubst t1_0 t2_0
    case runTcM go of
      Left _ -> panic (text "Arg")
      Right r -> r
  where
    check s t1 t2 | trace (pretty (s, t1, t2)) False = undefined
    check s t1 t2@(TyVar v)
      | v `S.member` foralls =
          case s !! v of
            Nothing -> Just $ addTySubstBinding s v t1
            Just t' ->
                if t1 == t' then Just s else Nothing
      | t1 == t2           = Just s
    check s t1@(TyCon _) t2@(TyCon _)
      | t1 == t2           = Just s
    check s (TyApp t1a t1b) (TyApp t2a t2b) = do
      s' <- check s t1a t2a
      check s' t1b t2b
    check _ _ _ = Nothing

    foralls = S.fromList tvs2
--    skolems = S.fromList tvs1

    go = do
      skolems <- 
          forM tvs1 $ \x -> do
            -- FIXME: This way of generating names is not very
            -- reliable, because we might just end up with the same
            -- unique as the input variable.
            --
            -- A possible solution might be to "tag" a unique like GHC does.
            -- I.e., set the top 8 bits of the unique to something that is
            -- used nowhere else in the compiler.
            --
            -- Alternatively, we could distinguish type vars.  E.g., TyVar,
            -- Skolem, ...
            x' <- TyVar <$> (freshTyVar . ("skol_"++) . idString . tyVarId $ x)
            return (x, x')
      return (check emptyTySubst (apply (tySubstFromList skolems) t1_0) t2_0)
-}
-- * Generating well-typed terms


-- TODO: how to ensure that var is of the proper type?
var :: [(Id, Type)] -> Type -> Gen Expr
var env t0 = do
  (v, t) <- elements env
  return $ EVar noSrcSpan v --, t)
  
-- All free variables in the result will be skolems, and can therefore be
-- forall-quantified to yield a type scheme.
genTerm :: Type -> Gen Expr
genTerm _ = return undefined

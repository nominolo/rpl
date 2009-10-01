module RPL.Test.Parser where

import RPL.Test.TestUtils

import RPL.Syntax hiding ( mkId )
import RPL.Lexer hiding ( main )
import RPL.Parser
import RPL.Utils.SrcLoc
import RPL.Error
import RPL.Utils.Unique

import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit
--import Test.Framework.Providers.QuickCheck (testProperty)

import Test.HUnit

tokens :: String -> Either ErrorMessage [Located Token]
tokens s = 
  case lexTokenStream (stringInput s) (startLoc "<stdin>") of
    Left e -> Left (errMsg e)
    Right ts -> Right ts

parse_success :: (Show a, Eq a) => ParseM a -> String -> a -> Assertion
parse_success p inp expect = do
  runParseM p (stringInput inp) dummyLoc @?= Right expect

u :: SrcSpan
u = mkSrcSpan dummyLoc dummyLoc

mkId :: String -> Id
mkId x = Id (uniqueFromInt 0) x

tests :: [F.Test]
tests = [ testGroup "parse" $
  [ testGroup "pattern" $
    [ testCase "var" $
        parse_success parsePat "x"
          (VarPat u (mkId "x"))
    ]
  , testGroup "type" $
    [ testCase "var" $
        parse_success parseType "x"
          (TVar u (mkId "x"))
    , testCase "con" $
        parse_success parseType "X"
          (TCon u (mkId "X"))
    , testCase "app" $
        parse_success parseType "X x"
          (TApp u (TCon u (mkId "X")) (TVar u (mkId "x")))
    , testCase "fun" $
        parse_success parseType "Int -> Int"
          (TFun u (TCon u (mkId "Int")) (TCon u (mkId "Int")))
    , testCase "forall" $
        parse_success parseType "forall a . a"
          (TAll u (mkId "a") (TVar u (mkId "a")))
    ]
  , testGroup "expression" $
    [ testCase "var" $
        parse_success parseExpr "x"
          (EVar u (mkId "x"))
    , testCase "lit" $
      parse_success parseExpr "1"
        (ELit u (IntLit 1))
    , testCase "app" $
        parse_success parseExpr "f x"
          (EApp u (EVar u (mkId "f")) (EVar u (mkId "x")))
    , testCase "lam" $
        parse_success parseExpr "\\x -> y"
          (ELam u (VarPat u (mkId "x")) (EVar u (mkId "y")))
    , testCase "let" $
        parse_success parseExpr "let f = \\x -> x in f"
          (ELet u (VarPat u (mkId "f"))
              (ELam u (VarPat u (mkId "x")) (EVar u (mkId "x")))
            (EVar u (mkId "f")))
    , testCase "ann" $
        parse_success parseExpr "x :: forall a. a -> a"
          (EAnn u (EVar u (mkId "x"))
                  (TAll u (mkId "a") (TFun u (TVar u (mkId "a")) (TVar u (mkId "a")))))
    ]
  ] ]

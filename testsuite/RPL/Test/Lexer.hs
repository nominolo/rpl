module RPL.Test.Lexer where

import RPL.Test.Utils

import RPL.Lexer hiding ( main )
import RPL.Utils.SrcLoc
import RPL.Error

import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit
--import Test.Framework.Providers.QuickCheck (testProperty)

import Test.HUnit


tokens :: String -> Either ErrorMessage [Located Token]
tokens s = 
  case lexTokenStream (stringInput s) (startLoc "<stdin>") of
    Left e -> Left (errMsg e)
    Right ts -> Right ts

tests :: [F.Test]
tests = [ testGroup "tokens" $
  [ testCase "markers" $
      tokens_success
        "\\ = -> :: ( )"
        [TokLambda,TokEqual,TokRArrow,TokDblColon,TokOParen,TokCParen]

  , testCase "keywords" $
      tokens_success
        "let in data where case of"
        [TokLet,TokIn,TokData,TokWhere,TokCase,TokOf]
  
  , testCase "numbers" $
      tokens_success "0 1245" [TokInt 0,TokInt 1245]

  , testCase "identifier" $
      tokens_success "foo foo' goo fo'o Foo fOO f_oo f01"
        [TokVar "foo",TokVar "foo'",TokVar "goo",
         TokVar "fo'o",TokCon "Foo",TokVar "fOO",
         TokVar "f_oo",TokVar "f01"]

  , testGroup "no identifier"
      [ testCase "leading_quote" $
          tokens_failure "'foo" LexicalError
      , testCase "leading_digit" $
          tokens_success "0foo" [TokInt 0, TokVar "foo"]
      , testCase "leading_underscore" $
          tokens_failure "_oo" LexicalError
      ]
  ] ]

tokens_success :: String -> [Token] -> Assertion
tokens_success str toks =
  fmap (map unLoc) (tokens str) @?= Right toks

tokens_failure :: String -> ErrorMessage -> Assertion
tokens_failure str msg = tokens str @?= Left msg

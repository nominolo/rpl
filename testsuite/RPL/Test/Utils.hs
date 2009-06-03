module RPL.Test.Utils where

import RPL.Utils.UnionFind

import Test.Framework as F (testGroup, Test)
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Control.Monad ( unless )
import Data.List ( nub )
import Test.HUnit
import Test.QuickCheck
import Test.QuickCheck.Monadic as QC

------------------------------------------------------------------------

tests :: [F.Test]
tests = [ testGroup "union-find" $
  [ testCase "fresh/equal" $
      do p <- fresh "a"
         b <- equivalent p p
         b @? "Fresh element is equal to itself"
  , testCase "fresh/distinct" $
      do p <- fresh "a"; p' <- fresh "b"
         b <- equivalent p p'
         not b @? "Two fresh elements are distinct"
  , testCase "union" $
      do p <- fresh "a"; p' <- fresh "b"
         union p p'
         b <- equivalent p p'
         b @? "Fresh union implies equivalence"
  ] ]

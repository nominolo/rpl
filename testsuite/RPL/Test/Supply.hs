module RPL.Test.Supply where

import Data.Supply

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
tests = [ testGroup "supply" $
  [ testCase "init" $
      do s0 <- newSupply (0 :: Int) (1+)
         supplyValue s0 @?= 0
  , testCase "split2" $
      do (s1,s2) <- split2 `fmap` newSupply (0 :: Int) (1+)
         assertNotEqual "Split result" (supplyValue s1) (supplyValue s2)
  , testCase "split2/2" $
      do (s1,s2) <- split2 `fmap` newSupply (0 :: Int) (1+)
         let (s1',s1'') = split2 s1
         let (s2',s2'') = split2 s2
         allDifferent $ map supplyValue [s1, s1', s1'', s2, s2', s2'']
  , testProperty "split_n" prop_split
  ]]

prop_split :: Property
prop_split =
    monadicIO $
    forAllM (arbitrary :: Gen Int) $ \ini ->
      forAllM (choose (0 :: Int, 100)) $ \prefix -> do
        s0 <- run $ newSupply ini (1+)
        let as = map supplyValue $ take prefix $ split s0
        QC.assert (length as == length (nub as))
         
assertNotEqual :: (Eq a, Show a) => String -> a -> a -> Assertion
assertNotEqual preface inp1 inp2 =
  unless (inp1 /= inp2) (assertFailure msg)
 where msg = (if null preface then "Inputs" else preface) ++
             " expected to be different.\n" ++
             "However, both were: " ++ show inp1

allDifferent :: (Eq a, Show a) => [a] -> Assertion
allDifferent as =
    unless (length as == length (nub as)) $ assertFailure msg
  where 
    msg = "Values were not all different.  Inputs were:\n  " ++ 
          show as

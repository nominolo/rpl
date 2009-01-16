{-# LANGUAGE FlexibleInstances #-}
module RPL.Names where

import RPL.Utils.Pretty
import RPL.Utils.Unique

-- Testing
import Test.QuickCheck
import Data.Char ( ord, toUpper )

------------------------------------------------------------------------

-- | An identifier.
data Id = Id !Unique String
  deriving (Eq, Show, Ord)

idString :: Id -> String
idString (Id _ n) = n

instance Pretty Id where
  ppr (Id u v) = text v <> ifDebugStyle (char '_' <> ppr u)

------------------------------------------------------------------------

newtype Uppercase a = Uppercase a

instance Arbitrary Id where arbitrary = arbLowercase
instance Arbitrary (Uppercase Id) where
  arbitrary = Uppercase `fmap` arbUppercase

arbLowercase = do
   n <- sized (\n -> elements (take n simpleNames))
   let i = product (map ord n)
   return (Id (uniqueFromInt i) n)

arbUppercase = do
   n <- fmap (map toUpper) $ sized (\n -> elements (take n simpleNames))
   let i = product (map ord n)
   return (Id (uniqueFromInt i) n)

simpleNames :: [String]
simpleNames = go 1
  where
    go n = sn n ++ go (n+1)
    sn :: Int -> [String] -- names of length `n`
    sn 0 = [""]
    sn n = [ x:xs | x <- ['a'..'z'], xs <- sn (n-1) ]

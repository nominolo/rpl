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

isBuiltInName :: Id -> Bool
isBuiltInName (Id u _) = intFromUnique u < 100

instance Pretty Id where
  ppr n@(Id u v) =
     text v <> ifDebugStyle (if isBuiltInName n then empty else ppr u)

-- | For an arbitrary infix operator `<>` defines how an expression
-- 
--     a <> b <> c
--
-- is being parsed.
data Associativity
  = AssocLeft   -- ^ Parse as `(a <> b) <> c`
  | AssocRight  -- ^ Parse as `a <> (b <> c)`
  | AssocNone   -- ^ Expression is ambiguous, explicit parentheses are
                -- needed.

------------------------------------------------------------------------

newtype Uppercase a = Uppercase a

instance Arbitrary Id where arbitrary = arbLowercase
instance Arbitrary (Uppercase Id) where
  arbitrary = Uppercase `fmap` arbUppercase

arbLowercase = do
   n <- sized (\n -> elements (take (n+1) simpleNames))
   let i = product (map ord n)
   return (Id (uniqueFromInt i) n)

arbUppercase = do
   n <- fmap (map toUpper) $ sized (\n -> elements (take (n+1) simpleNames))
   let i = product (map ord n)
   return (Id (uniqueFromInt i) n)

simpleNames :: [String]
simpleNames = go 1
  where
    go n = sn n ++ go (n+1)
    sn :: Int -> [String] -- names of length `n`
    sn 0 = [""]
    sn n = [ x:xs | x <- ['a'..'z'], xs <- sn (n-1) ]

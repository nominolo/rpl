module RPL.Utils.Unique (
  Unique,
  uniqueFromInt,
) where

import RPL.Utils.Pretty

newtype Unique = Unique Int
  deriving (Eq, Ord, Show)

instance Pretty Unique where
  ppr (Unique u) = int u

uniqueFromInt :: Int -> Unique
uniqueFromInt n = Unique n
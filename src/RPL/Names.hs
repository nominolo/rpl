module RPL.Names where

import RPL.Utils.Pretty

-- | An identifier.
data Id = Id String
  deriving (Show)

instance Pretty Id where
  ppr (Id v) = text v


module RPL.Names where

import RPL.Utils.Pretty

-- | An identifier.
data Id = Id String
  deriving (Eq, Show, Ord)

idString :: Id -> String
idString (Id n) = n

instance Pretty Id where
  ppr (Id v) = text v


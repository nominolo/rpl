module RPL.Names where

import RPL.Utils.Pretty
import RPL.Utils.Unique

-- | An identifier.
data Id = Id !Unique String
  deriving (Eq, Show, Ord)

idString :: Id -> String
idString (Id _ n) = n

instance Pretty Id where
  ppr (Id u v) = text v <> char '_' <> ppr u


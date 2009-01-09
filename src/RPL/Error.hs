-- | Error codes and such.
--
module RPL.Error where

import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

------------------------------------------------------------------------

data SourceError = SourceError SrcSpan ErrorMessage
  deriving (Eq, Show)

data ErrorMessage
  = LexicalError
  | ParseError
  deriving (Eq, Show)

------------------------------------------------------------------------

instance Pretty SourceError where
  ppr (SourceError s m) = 
      ppr s <> colon $$ nest 4 (ppr m)

instance Pretty ErrorMessage where
  ppr m = case m of
    LexicalError -> wrappingText "lexical error"
    ParseError -> wrappingText "parse error"

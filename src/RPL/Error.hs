-- | Error codes and such.
--
module RPL.Error where

import RPL.Names
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty

------------------------------------------------------------------------
-- FIXME: Use extensible data type. 

data SourceError
  = SourceError { errSpan :: SrcSpan
                , errMsg  :: ErrorMessage }
  deriving (Eq, Show)

data ErrorMessage
  = LexicalError
  | ParseError
  | NotInScope Id
  | TypeMismatch String String
  | MultiplePatVars [Id]
  deriving (Eq, Show)

------------------------------------------------------------------------

instance Pretty SourceError where
  ppr (SourceError s m) = 
      ppr s <> colon $$ nest 4 (ppr m)

instance Pretty ErrorMessage where
  ppr m = case m of
    LexicalError -> wrappingText "lexical error"
    ParseError -> wrappingText "parse error"
    NotInScope name ->
        hang (wrappingText "Not in scope" <> colon) 2 (ppr name)
    TypeMismatch t1 t2 ->
        wrappingText "Could not match expected type:" $$
        nest 4 (text t1) $$
        wrappingText "Against inferred type:" $$
        nest 4 (text t2)
    MultiplePatVars vs ->
        wrappingText "Multiple occurrences of pattern variables:" $$
        nest 4 (fsep (commaSep (map ppr vs)))

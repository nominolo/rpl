--                                                              -*-haskell-*-
-- ---------------------------------------------------------------------------
{
{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# LANGUAGE BangPatterns #-}

module RPL.Lexer where

import RPL.Utils.Monads
import RPL.Utils.SrcLoc
import RPL.Utils.Pretty
import RPL.Error

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Lazy.UTF8 as UTF8

import Control.Applicative
import Control.Monad ( liftM )
import Data.Int      ( Int64 )

}

$digit = 0-9
$alpha = [a-zA-Z]
$lower = [a-z]
$upper = [A-Z]

tokens :-

  $white+                         ;
  "--".*                          ;
  let                             { \s _ -> return $ L s TokLet }
  in                              { \s _ -> return $ L s TokIn }
  data                            { \s _ -> return $ L s TokData }
  where                           { \s _ -> return $ L s TokWhere }
  case                            { \s _ -> return $ L s TokCase }
  of                              { \s _ -> return $ L s TokOf }
  $digit+                         { \s t -> return $ L s (TokInt (read t)) }
  "."                             { \s _ -> return $ L s TokDot }
  "="                             { \s _ -> return $ L s TokEqual }
  \\                              { \s _ -> return $ L s TokLambda }
  "->"                            { \s _ -> return $ L s TokRArrow }
  "::"                            { \s _ -> return $ L s TokDblColon }
  "("                             { \s _ -> return $ L s TokOParen }
  ")"                             { \s _ -> return $ L s TokCParen }
  $lower [$alpha $digit \_ \']*   { \s t -> return $ L s (TokVar t) }
  $upper [$alpha $digit \_ \']*   { \s t -> return $ L s (TokCon t) }
  [\* \/ \+ \- \= \~ \^ \& \!]+   { \s t -> return $ L s (TokOper t) }

{
------------------------------------------------------------------------
-- * The Parser Monad

-- | The parser monad.
--
-- It is implemented as state+CPS monad with two continuations: one for
-- success, one for failure.
-- 
type ParseM a = StrictStateErrorM LexState SourceError a

-- | Signal an error in the parse monad.  Immediately aborts parsing.
parseMError :: SrcSpan -> ErrorMessage -> ParseM a
parseMError span err = throwError (SourceError span err)

-- ** The Lexer State

data LexState = LexState
  { lex_pos  :: !SrcLoc
    -- ^ Position at current input location.
  , lex_inp  :: UTF8.ByteString
    -- ^ The current input.
  , lex_offs :: {-#UNPACK#-} !Int64
    -- ^ Byte offset since the start of buffer.  Stored in the 'SrcLoc'.
  , lex_chr  :: {-#UNPACK#-} !Char
    -- ^ the character before the input (the look-ahead)
  , lex_scd  :: {-#UNPACK#-} !Int
    -- ^ The current start code (i.e., lexer state).
  , lex_last_loc :: SrcSpan
    -- ^ Location of last token.  Used for reporting parse errors.
  }

-- | Set the location of the last token.  This is used as the position in
-- case of a parse error.
setLastLoc :: SrcSpan -> ParseM ()
setLastLoc span = modify $ \s -> s { lex_last_loc = span }

-- ** The interface for Alex

data AlexInput 
  = AI SrcLoc              -- current position
       {-#UNPACK#-} !Int64 -- byte offset
       {-#UNPACK#-} !Char  -- previous char
       UTF8.ByteString        -- current input string

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (AI _ _ c _) = c

alexGetChar :: AlexInput -> Maybe (Char,AlexInput)
alexGetChar (AI p o _ bs) =
  case UTF8.decode bs of
    Nothing -> Nothing
    Just (c, len) ->
        let !bs' = UTF8.drop len bs
            !p'  = advanceSrcLoc p c
            !o'  = o + len
        in Just (c, AI p' o' c bs')

-- * Our utils

getInput :: ParseM AlexInput
getInput = do s <- get
              return (AI (lex_pos s) (lex_offs s) (lex_chr s) (lex_inp s))

setInput :: AlexInput -> ParseM ()
setInput (AI p o c bs) = do
    modify (\s -> s { lex_pos = p, lex_chr = c, lex_inp = bs, lex_offs = o })
                       
getLexState :: ParseM Int
getLexState = gets lex_scd

lexToken :: ParseM (Located Token)
lexToken = do
  inp@(AI loc1 offs1 _ bs) <- getInput
  sc <- getLexState
  case alexScan inp sc of
    AlexEOF -> do
      let span = mkSrcSpan loc1 loc1
      setLastLoc span
      return (L span TokEof)
    AlexError (AI loc2 _ _ bs') -> do
      let span = mkSrcSpan loc1 loc2
      setLastLoc span
      parseMError span LexicalError
    AlexSkip inp2 _ -> do
      setInput inp2
      lexToken
    AlexToken inp2@(AI loc2 offs2 _ bs') _ t -> do
      setInput inp2
      let !span = mkSrcSpan loc1 loc2
      let bytes = offs2 - offs1
      setLastLoc span
      t span (UTF8.toString (UTF8.take bytes bs))

lexer :: (Located Token -> ParseM a) -> ParseM a
lexer cont = do
  tok@(L _span _tok__) <- lexToken
--  trace ("token: " ++ show tok__) $ do
  cont tok

runParseM :: ParseM a 
        -> UTF8.ByteString -> SrcLoc 
        -> Either SourceError a
runParseM m buf loc = runStrictStateErrorM m initState
  where
    initState = LexState loc buf 0 '\n' 0 noSrcSpan

-- | TODO: This may be too strict, if the result type were
--
--     (Maybe SourcError, [Located Token])
--
-- the partial result could be extracted even in the case of an error.
lexTokenStream :: UTF8.ByteString -> SrcLoc 
               -> Either SourceError [Located Token]
lexTokenStream buf loc = runStrictStateErrorM go initState
  where
    initState = LexState loc buf 0 '\n' 0 noSrcSpan
    go = do
      ltok <- lexer return
      case ltok of
        L _ TokEof -> return []
        _ -> liftM (ltok:) go

parseFail :: ParseM a
parseFail = do
    s <- get
    parseMError (lex_last_loc s) ParseError

-- | The token type
data Token 
  = TokLet
  | TokIn
  | TokData
  | TokWhere
  | TokCase
  | TokOf
  | TokSym Char
  | TokDot
  | TokEqual
  | TokLambda
  | TokRArrow
  | TokDblColon
  | TokOParen
  | TokCParen
  | TokVar String
  | TokCon String
  | TokOper String
  | TokInt Int
  | TokEof
  deriving (Eq,Show)

instance Pretty Token where
  ppr t = text (show t) -- TODO

main = do
  s <- BS.getContents
  print (lexTokenStream s (startLoc "<stdin>"))
}

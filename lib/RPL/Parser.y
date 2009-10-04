--                                                              -*-haskell-*-
-- ---------------------------------------------------------------------------
{
{-# OPTIONS_GHC -w #-}
module RPL.Parser ( parseProgram, parseExpr, parseType, parsePat, parseDecl ) where

import RPL.Lexer
import RPL.Syntax
import RPL.Error
import RPL.Utils.SrcLoc
import RPL.Utils.Unique
}

%token
 'let'           { L _ TokLet }
 'in'            { L _ TokIn }
 '.'             { L _ TokDot }
 '='             { L _ TokEqual }
 '\\'            { L _ TokLambda }
 '->'            { L _ TokRArrow }
 '('             { L _ TokOParen }
 ')'             { L _ TokCParen }
 '{'             { L _ TokOBrace }
 '}'             { L _ TokCBrace }
 ';'             { L _ TokSemicolon }
 '::'            { L _ TokDblColon }
 'forall'        { L _ (TokVar "forall") }
 'data'          { L _ TokData }
 'where'         { L _ TokWhere }

VARID            { L _ (TokVar _) }
CONID            { L _ (TokCon _) }
INTEGER          { L _ (TokInt _) }

%monad { ParseM } { >>= } { return }
%lexer { lexer } { L _ TokEof }
%name parseProgram program
%name parseExpr exp
%name parseType ctyp
%name parsePat pat
%name parseDecl decl
%tokentype { (Located Token) }
%%

-- * Main Entry Point

program :: { Program }
        : decls exp      { Program $1 $2 }

-- * Declarations

decls  :: { [Decl] }
        : {- empty -}    { [] }
        | decl decls     { $1 : $2 }

decl   :: { Decl }
        : 'data' con vars 'where' '{' datacon_decls '}'
                         { let loc = getSpan $1 `combineSpans` getSpan $7 in
                           let con_id = unLoc $2 in
                           let vars = map unLoc $3 in
                           DataDecl loc con_id vars $6 }

datacon_decls :: { [DataConDecl] }
  : datacon_decl         { [$1] }
  | datacon_decl ';'
    datacon_decls        { $1 : $3 }

datacon_decl :: { DataConDecl }
  : con '::' ctyp        { let con_id = unLoc $1 in
                           let loc = getSpan $1 `combineSpans` getSpan $3 in
                           DataConDecl loc con_id $3 }

-- * Expressions

-- ** Variables

vars   :: { [Located Id] }
        : {- empty -}     { [] }
        | var vars        { $1 : $2 }

var    :: { Located Id }
        : VARID          { let L s (TokVar n) = $1 in
                           L s (Id (uniqueFromInt 0) n) } -- XXX: better unique

con    :: { Located Id }
        : CONID          { let L s (TokCon n) = $1 in
                           L s (Id (uniqueFromInt 0) n) } -- XXX: better unique

-- ** Literals

literal :: { Located Lit }
         : INTEGER       { let L s (TokInt i) = $1 in L s (IntLit i) }

-- ** Other Expressions

exp     :: { Expr }
        : exp0 '::' ctyp            { let s1 = exprSpan $1 in
                                      let s2 = typeSpan $3 in
                                      let s = combineSpans s1 s2 in
                                      EAnn s $1 $3 }
        | exp0                      { $1 }

exp0    :: { Expr }
        : exp10                     { $1 }

exp10  :: { Expr }
     : 'let' pat '=' exp 'in' exp   { let s1 = getLoc $1 in
                                      let s2 = exprSpan $6 in
                                      let s = combineSpans s1 s2 in
                                      ELet s $2 $4 $6 }
     | '\\' pats '->' exp           { mkLam (getLoc $1) $2 $4 }
     | fexp                         { $1 }

fexp   :: { Expr }
     : aexp                         { $1 }
     | fexp aexp                    { let s = exprSpan $1 `combineSpans` exprSpan $2
                                      in EApp s $1 $2 }

aexp   :: { Expr }
     : var                          { let v = unLoc $1 in
                                      let s = getLoc $1 in
                                      EVar s v }
     | con                          { EVar (getLoc $1) (unLoc $1) }
     | literal                      { let l = unLoc $1 in
                                      let s = getLoc $1 in
                                      ELit s l }
     | '(' exp ')'                  { $2 }

-- * Patterns

pats :: { [Pat] }
     : {- empty -}                  { [] }
     | pat pats                     { $1 : $2 }

pat :: { Pat }
     : var                          { let v = unLoc $1 in
                                      let s = getLoc $1 in
                                      VarPat s v }


ctyp :: { Type }
     : 'forall' var '.' ctyp        { let s = combineSpans (getLoc $1) (typeSpan $4) in
                                      TAll s (unLoc $2) $4 }
     | typ                          { $1 }


typ :: { Type }
     : btyp                         { $1 }
     | btyp '->' ctyp               { let s = combineSpans (typeSpan $1) (typeSpan $3) in
                                      TFun s $1 $3 }

btyp :: { Type }
     : btyp atyp                    { let s = combineSpans (typeSpan $1) (typeSpan $2) in
                                      TApp s $1 $2 }
     | atyp                         { $1 }

atyp :: { Type }
     : con                          { TCon (getLoc $1) (unLoc $1) }
     | var                          { TVar (getLoc $1) (unLoc $1) }
     | '(' ctyp ')'                 { $2 }
{
happyError :: ParseM a
happyError = parseFail
}

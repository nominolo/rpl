--                                                              -*-haskell-*-
-- ---------------------------------------------------------------------------
{
{-# OPTIONS_GHC -w #-}
module RPL.Parser ( parseProgram ) where

import RPL.Lexer
import RPL.Syntax
import RPL.Error
import RPL.Utils.SrcLoc
}

%token
 'let'           { L _ TokLet }
 'in'            { L _ TokIn }
 '='             { L _ TokEqual }
 '\\'            { L _ TokLambda }
 '->'            { L _ TokRArrow }
 '('             { L _ TokOParen }
 ')'             { L _ TokCParen }

VARID            { L _ (TokVar _) }
INTEGER          { L _ (TokInt _) }

%monad { ParseM } { >>= } { return }
%lexer { lexer } { L _ TokEof }
%name parseProgram program
%tokentype { (Located Token) }
%%

-- * Main Entry Point

program :: { Expr }
        : exp            { $1 }

-- * Expressions

-- ** Variables

var    :: { Located Id }
        : VARID          { let L s (TokVar n) = $1 in L s (Id n) }

-- ** Literals

literal :: { Located Lit }
         : INTEGER       { let L s (TokInt i) = $1 in L s (IntLit i) }

-- ** Other Expressions

exp     :: { Expr }
        : exp10                        { $1 }

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

{
happyError :: ParseM a
happyError = parseFail
}

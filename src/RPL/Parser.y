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

program :: { Expr }
        : exp            { $1 }

var    :: { Id }
        : VARID          { let L _ (TokVar n) = $1 in Id n }

literal :: { Lit }
         : INTEGER       { let L _ (TokInt i) = $1 in IntLit i }

exp    :: { Expr }
        : 'let' var '=' exp 'in' exp   { ELet $2 $4 $6 }
        | var                          { EVar $1 }
        | literal                      { ELit $1 }
        | '\\' var '->' exp            { ELam $2 $4 }
        | '(' exp ')'                  { $2 }

{
happyError :: ParseM a
happyError = parseFail
}

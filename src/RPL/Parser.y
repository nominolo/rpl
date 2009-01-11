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

var    :: { Id }
        : VARID          { let L _ (TokVar n) = $1 in Id n }

-- ** Literals

literal :: { Lit }
         : INTEGER       { let L _ (TokInt i) = $1 in IntLit i }

-- ** Other Expressions

exp     :: { Expr }
        : exp10                        { $1 }

exp10  :: { Expr }
     : 'let' var '=' exp 'in' exp   { ELet $2 $4 $6 }
     | '\\' pats '->' exp           { mkLam $2 $4 }
     | fexp                         { $1 }

fexp   :: { Expr }
     : aexp                         { $1 }
     | fexp aexp                    { EApp $1 $2 }

aexp   :: { Expr }
     : var                          { EVar $1 }
     | literal                      { ELit $1 }
     | '(' exp ')'                  { $2 }

-- * Patterns

pats :: { [Pat] }
     : {- empty -}                  { [] }
     | pat pats                     { $1 : $2 }

pat :: { Pat }
     : var                          { VarPat $1 }

{
happyError :: ParseM a
happyError = parseFail
}

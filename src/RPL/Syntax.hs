-- |
-- Module      : RPL.Syntax
-- Copyright   : (c) Thomas Schilling 2009
-- License     : BSD-style
--
-- Maintainer  : nominolo@googlemail.com
-- Stability   : experimental
-- Portability : portable
--
module RPL.Syntax where

import RPL.Utils.Pretty

------------------------------------------------------------------------
-- * Datatypes

-- | An identifier.
data Id = Id String
  deriving (Show)

-- | A Literal.
data Lit
  = IntLit Int
  | CharLit Char
  deriving (Show)

-- | An expression.
data Expr
  = ELit Lit             -- l
  | EVar Id              -- x
  | ELam [Pat] Expr      -- \ x_1 ... x_n -> E
  | EApp Expr Expr       -- E F
  | ELet Id Expr Expr    -- let x = E in F
  deriving (Show)

type Program = Expr

-- | A pattern.
data Pat
  = VarPat Id
  deriving (Show)

------------------------------------------------------------------------
-- * Pretty Instances

instance Pretty Id where
  ppr (Id v) = text v

instance Pretty Lit where
  ppr (IntLit i) = int i
  ppr (CharLit c) = text (show c)

instance Pretty Expr where
  ppr exp = case exp of
    ELit l -> ppr l
    EVar v -> ppr v
    ELam ps e -> 
        parens $
          hang (char '\\' <> sep (map ppr ps) <+> text "->") 2 (ppr e)
    EApp e1 e2 -> ppr_app e1 [e2]
    ELet v e1 e2 -> 
        text "let" <+> ppr v <+> char '=' <+> ppr e1 <+> text "in" $$
        ppr e2

-- | Only print outermost parens for nested applications. I. e.,
--
--     (((f x) y) z)   ~~>   (f x y z)
-- 
ppr_app :: Expr -> [Expr] -> Doc
ppr_app (EApp e1 e2) es = ppr_app e1 (e2 : es)
ppr_app f es            = parens (ppr f <+> sep (map ppr es))

instance Pretty Pat where
  ppr pat = case pat of
    VarPat v -> ppr v

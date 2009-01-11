-- |
-- Module      : RPL.Syntax
-- Copyright   : (c) Thomas Schilling 2009
-- License     : BSD-style
--
-- Maintainer  : nominolo@googlemail.com
-- Stability   : experimental
-- Portability : portable
--
module RPL.Syntax (
  module RPL.Syntax,
  module RPL.Names
) where

import RPL.Names
import RPL.Utils.Pretty

------------------------------------------------------------------------
-- * Datatypes

-- | A Literal.
data Lit
  = IntLit Int
  | CharLit Char
  deriving (Show)

-- | An expression.
data Expr
  = ELit Lit             -- l
  | EVar Id              -- x
  | ELam Pat Expr        -- \ x -> E
  | EApp Expr Expr       -- E F
  | ELet Id Expr Expr    -- let x = E in F
  deriving (Show)

mkLam :: [Pat] -> Expr -> Expr  -- \ x_1 ... x_n -> E
mkLam ps e = foldr ELam e ps

type Program = Expr

-- | A pattern.
data Pat
  = VarPat Id
  deriving (Show)

------------------------------------------------------------------------
-- * Pretty Instances

instance Pretty Lit where
  ppr (IntLit i) = int i
  ppr (CharLit c) = text (show c)

instance Pretty Expr where
  ppr exp = case exp of
    ELit l -> ppr l
    EVar v -> ppr v
    ELam p e -> ppr_lam e [p]
    EApp e1 e2 -> ppr_app e1 [e2]
    ELet v e1 e2 -> 
        text "let" <+> ppr v <+> char '=' <+> ppr e1 <+> text "in" $$
        ppr e2

ppr_lam (ELam p e) ps = ppr_lam e (p:ps)
ppr_lam e ps =
    parens $ hang (char '\\' <> sep (map ppr (reverse ps)) <+> text "->") 2 (ppr e)

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

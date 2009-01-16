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
import RPL.Utils.SrcLoc

------------------------------------------------------------------------
-- * Datatypes

-- | A Literal.
data Lit
  = IntLit Int
  | CharLit Char
  deriving (Show)

-- | An expression.
data Expr
  = ELit SrcSpan Lit             -- l
  | EVar SrcSpan Id              -- x
  | ELam SrcSpan Pat Expr        -- \ x -> E
  | EApp SrcSpan Expr Expr       -- E F
  | ELet SrcSpan Pat Expr Expr    -- let x = E in F
  deriving (Show)

exprSpan :: Expr -> SrcSpan
exprSpan exp = case exp of
  ELit s _     -> s
  EVar s _     -> s
  ELam s _ _   -> s
  EApp s _ _   -> s
  ELet s _ _ _ -> s

-- | Construct an expression from a lambda with multiple arguments.
--
--     \ x_1 ... x_n -> E   ~~>   \ x_1 -> \x_2 -> ... \x_n -> E
--
mkLam :: SrcSpan -- ^ Location of the "\"
      -> [Pat] -> Expr -> Expr  
mkLam _ [] e = e
mkLam loc (p:ps) exp = ELam (loc `combineSpans` l') p (go ps)
  where
    go []     = exp
    go (p:ps) = ELam (patSpan p `combineSpans` l') p (go ps)
    l' = exprSpan exp

type Program = Expr

-- | A pattern.
data Pat
  = VarPat SrcSpan Id
  deriving (Show)

patSpan :: Pat -> SrcSpan
patSpan pat = case pat of
  VarPat s _ -> s

------------------------------------------------------------------------
-- * Pretty Instances

instance Pretty Lit where
  ppr (IntLit i) = int i
  ppr (CharLit c) = text (show c)

instance Pretty Expr where
  ppr exp = case exp of
    ELit _ l -> ppr l
    EVar _ v -> ppr v
    ELam _ p e -> ppr_lam e [p]
    EApp _ e1 e2 -> ppr_app e1 [e2]
    ELet _ v e1 e2 -> 
        text "let" <+> ppr v <+> char '=' <+> ppr e1 <+> text "in" $$
        ppr e2

ppr_lam (ELam _ p e) ps = ppr_lam e (p:ps)
ppr_lam e ps =
    parens $ hang (char '\\' <> sep (map ppr (reverse ps)) <+> text "->") 2 (ppr e)

-- | Only print outermost parens for nested applications. I. e.,
--
--     (((f x) y) z)   ~~>   (f x y z)
-- 
ppr_app :: Expr -> [Expr] -> PDoc
ppr_app (EApp _ e1 e2) es = ppr_app e1 (e2 : es)
ppr_app f es            = parens (ppr f <+> sep (map ppr es))

instance Pretty Pat where
  ppr pat = case pat of
    VarPat _ v -> ppr v

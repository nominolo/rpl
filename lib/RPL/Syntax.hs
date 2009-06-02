{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC #-}
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
import RPL.Utils.Panic

------------------------------------------------------------------------
-- * Datatypes

-- | A Literal.
data Lit
  = IntLit Int
  | CharLit Char
  deriving (Eq, Show)

-- | An expression.
data Expr
  = ELit SrcSpan Lit             -- l
  | EVar SrcSpan Id              -- x
  | ELam SrcSpan Pat Expr        -- \ x -> E
  | EApp SrcSpan Expr Expr       -- E F
  | ELet SrcSpan Pat Expr Expr   -- let x = E in F
  | EAnn SrcSpan Expr Type       -- (e :: t)
  deriving (Eq, Show)

data Type
  = TVar SrcSpan Id
  | TCon SrcSpan Id
  | TApp SrcSpan Type Type
  | TFun SrcSpan Type Type
  | TAll SrcSpan Id Type
  deriving (Eq, Show)

-- | Return the source span of an expression.
exprSpan :: Expr -> SrcSpan
exprSpan expr = case expr of
  ELit s _     -> s
  EVar s _     -> s
  ELam s _ _   -> s
  EApp s _ _   -> s
  ELet s _ _ _ -> s
  EAnn s _ _   -> s

typeSpan :: Type -> SrcSpan
typeSpan ty = case ty of
  TVar s _    -> s
  TCon s _    -> s
  TFun s _ _  -> s
  TAll s _ _  -> s
  TApp s _ _  -> s

-- | Construct a multi-argument lambda.
--
-- @
-- \ x_1 ... x_n -> E   ~~>   \ x_1 -> \x_2 -> ... \x_n -> E
-- @
mkLam :: SrcSpan -- ^ Location of the @\\@
      -> [Pat] -> Expr -> Expr  
mkLam _ [] e = e
mkLam loc (p:ps) expr = ELam (loc `combineSpans` l') p (go ps)
  where
    go []     = expr
    go (p':ps') = ELam (patSpan p' `combineSpans` l') p' (go ps')
    l' = exprSpan expr

-- | Construct nested applications from an n-ary application. I.e., 
--
-- > mkApp f [x,y,z] = (((f x) y) z)
mkApp :: Expr -> [Expr] -> Expr
mkApp fun [] = fun
mkApp fun (e:es) =
    let e' = EApp (exprSpan fun `combineSpans` exprSpan e) fun e in
    e' `seq` mkApp e' es

type Program = Expr

-- | A pattern.
data Pat
  = VarPat SrcSpan Id -- ^ Single variable pattern.
  deriving (Eq, Show)

-- | Return source span of a pattern.
patSpan :: Pat -> SrcSpan
patSpan pat = case pat of
  VarPat s _ -> s

------------------------------------------------------------------------
-- * Views

-- | View nested unary applications as n-ary applications.  I.e.,
--
-- > viewApp (((f x) y) z) = (f, [x,y,z])
--
-- Inverse of 'mkApp'.
viewApp :: Expr -> (Expr, [Expr])
viewApp (EApp _ e1_0 e2_0) = go e1_0 [e2_0]
  where
    go (EApp _ e1 e2) args = go e1 (e2 : args)
    go fun_expr       args = (fun_expr, args)
viewApp expr = panic $
    text "viemMultiApp can only be applied to expressions of the form (EApp ...)"
     $+$
    text "Input was:" <+> text (show expr)

------------------------------------------------------------------------
-- * Pretty Instances

instance Pretty Lit where
  ppr (IntLit i) = int i
  ppr (CharLit c) = text (show c)

instance Pretty Expr where
  ppr expr = case expr of
    ELit _ l -> ppr l
    EVar _ v -> ppr v
    ELam _ p e -> ppr_lam e [p]
    EApp _ _ _ -> ppr_app expr
    ELet _ v e1 e2 -> 
        keyword "let" <+> ppr v <+> char '=' <+> ppr e1 <+> keyword "in" $$
        ppr e2
    EAnn _ e t -> parens $ ppr e <+> text "::" <+> ppr t

instance Pretty Type where
  ppr ty = case ty of
    TVar _ v -> ppr v
    TCon _ tc -> ppr tc
    TFun _ t1 t2 -> ppr t1 <+> text "->" <+> ppr t2
    TAll _ x t -> text "forall" <+> ppr x <> char '.' <+> ppr t
    TApp _ t1 t2 -> ppr t1 <+> ppr t2

-- Combine nested lambdas into one top-level lambda.  I.e.,
--
-- > \x -> \y -> foo
--
-- is printed as
--
-- > \x y -> foo
--
-- TODO: don't do this if we have shadowed bindings (i.e. @\x -> \x -> ...@)
ppr_lam :: Expr -> [Pat] -> PDoc
ppr_lam inner_expr outer_pats =
  case inner_expr of
    ELam _ pat e -> ppr_lam e (pat : outer_pats)
    _otherwise -> 
      parens $ hang (char '\\' <> sep (map ppr (reverse outer_pats))
                              <+> text "->")
                    2 (ppr inner_expr)

-- | Only print outermost parens for nested applications. I. e.,
--
-- > (((f x) y) z)   ~~>   (f x y z)
-- 
ppr_app :: Expr -> PDoc
ppr_app expr | (f, es) <- viewApp expr = parens (ppr f <+> sep (map ppr es))


instance Pretty Pat where
  ppr pat = case pat of
    VarPat _ v -> ppr v

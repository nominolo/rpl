module RPL.Typecheck.HMX.Core where

import qualified RPL.Utils.UnionFind as UF
import RPL.Utils.Pretty

import Control.Applicative
import Data.Foldable
import Data.Traversable

-- | An \"abstract recursive type\"-- a fixed point combinator that adds
-- variables.
--
-- This type takes the 'Term' data type and puts itself inside the recursive
-- holes.
-- 
data ArTerm var
  = TVar var
  | TTerm (Term (ArTerm var))

instance Pretty var => Pretty (ArTerm var) where
  ppr (TVar v) = ppr v
  ppr (TTerm t) = ppr t

-- | The term algebra.
data Term r 
  = App r r
  | Var r  
  --  RowCons String r r | RowUniform r

instance Functor Term where
  fmap f (Var x)   = Var (f x)
  fmap f (App x y) = App (f x) (f y)

instance Foldable Term where
  foldr c e (Var x)   = x `c` e
  foldr c e (App x y) = x `c` (y `c` e)

instance Traversable Term where
  traverse f (Var x)   = Var <$> f x
  traverse f (App x y) = App <$> f x <*> f y

instance Pretty r => Pretty (Term r) where
  ppr (Var v)     = ppr v
  ppr (App t1 t2) = parens (ppr t1 <+> ppr t2)

------------------------------------------------------------------------


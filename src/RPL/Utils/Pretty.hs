-- |
-- Module      : RPL.Utils.Pretty
-- Copyright   : (c) Thomas Schilling 2009
-- License     : BSD-style
--
-- Maintainer  : nominolo@googlemail.com
-- Stability   : experimental
-- Portability : portable
--
module RPL.Utils.Pretty
  ( module RPL.Utils.Pretty
  , module Text.PrettyPrint
  )
where

import Text.PrettyPrint

------------------------------------------------------------------------
-- * The =Pretty= Class

class Pretty a where
  ppr :: a -> Doc

pretty :: Pretty a => a -> String
pretty x = render (ppr x)

pprint :: Pretty a => a -> IO ()
pprint x = putStrLn $ render $ ppr x

------------------------------------------------------------------------
-- * Combinators

-- | A string where words are automatically wrapped.
wrappingText :: String -> Doc
wrappingText msg = fsep $ map text $ words msg

------------------------------------------------------------------------
-- * Prelude Type Instances

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  ppr (Left a) = ppr a
  ppr (Right b) = ppr b

instance (Pretty a, Pretty b) => Pretty (a,b) where
  ppr (a,b) = parens (sep [ppr a <> comma, ppr b])

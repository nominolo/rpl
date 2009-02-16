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
  )
where

import qualified Text.PrettyPrint as P

import Data.Map ( Map )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Set as S

------------------------------------------------------------------------
-- * The =Pretty= Class

class Pretty a where
  ppr :: a -> PDoc

type PDoc = PrettyStyle -> P.Doc

data PrettyStyle
  = DebugStyle
  | UserStyle

pretty :: Pretty a => a -> String
pretty x = P.render (ppr x UserStyle)

pprint :: Pretty a => a -> IO ()
pprint x = putStrLn $ P.render $ ppr x UserStyle

debugPrint :: Pretty a => a -> IO ()
debugPrint x = putStrLn $ P.render $ ppr x DebugStyle

render :: PDoc -> String
render d = P.render (d UserStyle)

debugRender :: PDoc -> String
debugRender d = P.render (d DebugStyle)

------------------------------------------------------------------------
-- * Combinators

-- ** Primitives

empty :: PDoc
empty _ = P.empty

char :: Char -> PDoc
char c _ = P.char c

text :: String -> PDoc
text s _ = P.text s

int :: Int -> PDoc
int i _ = P.int i

infixl 6 <> 
infixl 6 <+>
infixl 5 $$, $+$

(<>) :: PDoc -> PDoc -> PDoc
(<>) d1 d2 sty = d1 sty P.<> d2 sty

(<+>) :: PDoc -> PDoc -> PDoc
(<+>) d1 d2 sty = d1 sty P.<+> d2 sty

($$) :: PDoc -> PDoc -> PDoc
($$) d1 d2 sty = d1 sty P.$$ d2 sty

($+$) :: PDoc -> PDoc -> PDoc
($+$) d1 d2 sty = d1 sty P.$+$ d2 sty

hcat :: [PDoc] -> PDoc
hcat ds sty = P.hcat (map ($ sty) ds)

hsep   :: [PDoc] -> PDoc
hsep ds sty = P.hsep (map ($ sty) ds)

vcat   :: [PDoc] -> PDoc
vcat ds sty = P.vcat (map ($ sty) ds)

cat    :: [PDoc] -> PDoc
cat ds sty = P.cat (map ($ sty) ds)

sep    :: [PDoc] -> PDoc
sep ds sty = P.sep (map ($ sty) ds)

fcat   :: [PDoc] -> PDoc
fcat ds sty = P.fcat (map ($ sty) ds)

fsep   :: [PDoc] -> PDoc
fsep ds sty = P.fsep (map ($ sty) ds)

nest   :: Int -> PDoc -> PDoc
nest n d sty = P.nest n (d sty)

-- | @hang d1 n d2 = sep [d1, nest n d2]@
hang :: PDoc -> Int -> PDoc -> PDoc
hang d1 n d2 sty = P.hang (d1 sty) n (d2 sty)

-- | @punctuate p [d1, ... dn] = [d1 \<> p, d2 \<> p, ... dn-1 \<> p, dn]@
punctuate :: PDoc -> [PDoc] -> [PDoc]
punctuate p [] = []
punctuate p (d:ds) = go d ds
  where go d []     = [d]
        go d (e:es) = (d <> p) : go e es

-- ** Parenthesis

parens :: PDoc -> PDoc
parens d sty = P.parens (d sty)

braces :: PDoc -> PDoc
braces d sty = P.braces (d sty)

brackets :: PDoc -> PDoc
brackets d sty = P.brackets (d sty)

angleBrackets :: PDoc -> PDoc
angleBrackets d = char '<' <> d <> char '>'

-- ** Symbols

comma :: PDoc
comma _ = P.comma

arrow :: PDoc
arrow _ = P.text "->"

colon _ = P.colon

-- | A string where words are automatically wrapped.
wrappingText :: String -> PDoc
wrappingText msg = fsep $ map text $ words msg

------------------------------------------------------------------------

-- ** Terminal Styles

ansiTermStyle :: String -> PDoc -> PDoc
ansiTermStyle ansi d sty =
  P.zeroWidthText ("\027[" ++ ansi ++ "m") P.<>
  d sty P.<>
  P.zeroWidthText "\027[0m"

ansiTermStyle2 :: String -> String -> PDoc -> PDoc
ansiTermStyle2 start end d sty =
  P.zeroWidthText ("\027[" ++ start ++ "m") P.<>
  d sty P.<>
  P.zeroWidthText ("\027[" ++ end ++ "m")

bold :: PDoc -> PDoc
bold = ansiTermStyle "1"

underline :: PDoc -> PDoc
underline = ansiTermStyle "4"

keyword :: String -> PDoc
keyword = bold . text

-- ** Style-specific Combinators

ifDebugStyle :: PDoc -> PDoc
ifDebugStyle d sty@DebugStyle = 
  ansiTermStyle "90" d sty
ifDebugStyle d _ = P.empty


-- ** Utils

commaSep :: [PDoc] -> [PDoc]
commaSep = punctuate comma

------------------------------------------------------------------------
-- * Prelude Type Instances

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  ppr (Left a) = ppr a
  ppr (Right b) = ppr b

instance (Pretty a, Pretty b) => Pretty (a,b) where
  ppr (a,b) = parens (sep [ppr a <> comma, ppr b])

instance Pretty s => Pretty (Set s) where
  ppr s = braces (fsep (punctuate comma (map ppr (S.toList s))))

instance Pretty a => Pretty [a] where
  ppr l = brackets (fsep (punctuate comma (map ppr l)))

instance (Pretty k, Pretty a) => Pretty (Map k a) where
  ppr s = braces (fsep (punctuate comma (map ppr_elem (M.toList s))))
    where ppr_elem (k, v) = ppr k <> colon <+> ppr v

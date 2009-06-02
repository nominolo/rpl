{-# OPTIONS_GHC -funbox-strict-fields #-}
-- |
-- Module      : RPL.Utils.SrcLoc
-- Copyright   : (c) Thomas Schilling 2009
-- License     : BSD-style
--
-- Maintainer  : nominolo@googlemail.com
-- Stability   : experimental
-- Portability : portable
--
module RPL.Utils.SrcLoc where

import RPL.Utils.Pretty

import Data.Bits ( (.&.), complement )

------------------------------------------------------------------------

type FastString = String -- TODO

------------------------------------------------------------------------
-- * Source Locations

-- | A location (a single point) in the source code.
--
-- A regular source location contains:
--
--   * filename (always an absolute path)
--
--   * line (starting at 1) and column (starting at 0), and
--
--   * total character offset from the beginning of the file.  (We count
--     decoded unicode characters, not bytes.)
--
-- Either of the last two points would be sufficient, however, some tools
-- work better with one while others work better with the other.
--
-- There's also an unhelpful location useful in cases where no useful
-- location can be given (should be used rarely).
data SrcLoc 
  = SrcLoc
       !FastString
       {-# UNPACK #-} !Int  -- Starts at 1
       {-# UNPACK #-} !Int  -- Starts at 0
       {-# UNPACK #-} !Int  -- Offset from beginning of buffer
  | UnhelpfulLoc FastString  -- Just a general indication
  deriving (Eq)

instance Pretty SrcLoc where
  ppr (SrcLoc s l c _) = text s <> colon <> int l <> colon <> int c
  ppr (UnhelpfulLoc s) = text s

-- | The first location in a file.  (Line 1, Column 0)
startLoc :: FastString -> SrcLoc
startLoc fnm = SrcLoc fnm 1 0 0

-- | Return new source location when moving past the given character.
--
-- Treats newlines and tabs specially.  Tabs advance to the next column that
-- is a multiple of 8.
advanceSrcLoc :: SrcLoc -> Char -> SrcLoc
advanceSrcLoc (SrcLoc f l c o) ch = case ch of
   '\t' -> SrcLoc f  l      (tab c)  (o+1)
   '\n' -> SrcLoc f  (l+1)  0        (o+1)
   _    -> SrcLoc f  l      (c+1)    (o+1)
  where
    tab chr = chr .&. complement 7 + 8
advanceSrcLoc loc _ = loc

-- | An unhelpful SrcLoc.  This is used for testing where we want to ignore
-- locations when comparing expressions.
dummyLoc :: SrcLoc
dummyLoc = UnhelpfulLoc ""

------------------------------------------------------------------------
-- * Source Regions

-- | A range of text in the source code.
--
-- Think of the start and end locations to refer to the space in *between*
-- two characters.  That is if line `L` contains the text
--
--     foobarbaz
--       ----
--
-- The underlined text ("obar") is the region `(L,2)-(L,6)` i.e. it starts
-- after the second character and ends after the sixth character.
--
data SrcSpan
    -- Because many spans only span one line or are even just one character
    -- long, it is worthwhile to have extra cases for these to save space.

  = SrcSpanOneLine 		-- a common case: a single line (L,C)-(L,C')
	{ srcSpanFile     :: !FastString,
	  srcSpanLine     :: {-# UNPACK #-} !Int,
	  srcSpanSCol     :: {-# UNPACK #-} !Int,
	  srcSpanECol     :: {-# UNPACK #-} !Int,
          srcSpanSOffs    :: {-# UNPACK #-} !Int,  -- Start offset
          srcSpanEOffs    :: {-# UNPACK #-} !Int   -- End offset
	}

  | SrcSpanMultiLine
	{ srcSpanFile	  :: !FastString,
	  srcSpanSLine    :: {-# UNPACK #-} !Int,
	  srcSpanSCol	  :: {-# UNPACK #-} !Int,
	  srcSpanELine    :: {-# UNPACK #-} !Int,
	  srcSpanECol     :: {-# UNPACK #-} !Int,
          srcSpanSOffs    :: {-# UNPACK #-} !Int,  -- Start offset
          srcSpanEOffs    :: {-# UNPACK #-} !Int   -- End offset
	}

  | SrcSpanPoint   -- (L,C)-(L,C+1)
	{ srcSpanFile	  :: !FastString,
	  srcSpanLine	  :: {-# UNPACK #-} !Int,
	  srcSpanCol      :: {-# UNPACK #-} !Int,
          srcSpanOffs     :: {-# UNPACK #-} !Int   -- Offset
	}

  | UnhelpfulSpan !FastString	-- Just a general indication
				-- also used to indicate an empty span
  deriving (Eq, Show)

instance Pretty SrcSpan where
  ppr sp = case sp of
    SrcSpanOneLine f l c1 c2 _ _ ->
        text f <> colon <> int l <> colon <> int c1 <> char '-' <> int c2
    SrcSpanMultiLine f l1 c1 l2 c2 _ _ ->
        text f <> colon <> int l1 <> colon <> int c1 <> char '-'
               <> int l2 <> colon <> int c2
    SrcSpanPoint f l c _ ->
        text f <> colon <> int l <> colon <> int c
    UnhelpfulSpan s -> text s

-- ** Constructing SrcSpans

-- | Construct a source span from two [SrcLoc]s.
mkSrcSpan :: SrcLoc -> SrcLoc -> SrcSpan
mkSrcSpan (UnhelpfulLoc str) _ = UnhelpfulSpan str
mkSrcSpan _ (UnhelpfulLoc str) = UnhelpfulSpan str
mkSrcSpan loc1 loc2
  | line1 == line2 = if col1 == col2
			then SrcSpanPoint file line1 col1 offs1
			else SrcSpanOneLine file line1 col1 col2 offs1 offs2
  | otherwise      = SrcSpanMultiLine file line1 col1 line2 col2 offs1 offs2
 where
   SrcLoc file line1 col1 offs1 = loc1
   SrcLoc _    line2 col2 offs2 = loc2

noSrcSpan :: SrcSpan
noSrcSpan = UnhelpfulSpan "<no location info>"

extendLeft :: SrcLoc -> SrcSpan -> SrcSpan
extendLeft l s = mkSrcSpan l (srcSpanEndLoc s)

extendRight :: SrcSpan -> SrcLoc -> SrcSpan
extendRight s l = mkSrcSpan (srcSpanStartLoc s) l

combineSpans :: SrcSpan -> SrcSpan -> SrcSpan
combineSpans s1 s2 = mkSrcSpan (srcSpanStartLoc s1) (srcSpanEndLoc s2)

-- ** Selectors

srcSpanStartLoc :: SrcSpan -> SrcLoc
srcSpanStartLoc (UnhelpfulSpan s)                   = UnhelpfulLoc s
srcSpanStartLoc (SrcSpanOneLine f l c1 _ o1 _)      = SrcLoc f l c1 o1
srcSpanStartLoc (SrcSpanMultiLine f l1 c1 _ _ o1 _) = SrcLoc f l1 c1 o1
srcSpanStartLoc (SrcSpanPoint f l c o)              = SrcLoc f l c o

srcSpanEndLoc :: SrcSpan -> SrcLoc
srcSpanEndLoc (UnhelpfulSpan s)                   = UnhelpfulLoc s
srcSpanEndLoc (SrcSpanOneLine f l _ c2 _ o2)      = SrcLoc f l c2 o2
srcSpanEndLoc (SrcSpanMultiLine f _ _ l2 c2 _ o2) = SrcLoc f l2 c2 o2
srcSpanEndLoc (SrcSpanPoint f l c o)              = SrcLoc f l c o

------------------------------------------------------------------------

-- | Wrapper to add source locations to an element.
data Located e 
  = L { getLoc :: SrcSpan, -- ^ Return location of the element.
        unLoc  :: e        -- ^ Extract wrapped element.
      }
  deriving (Show, Eq)

instance Pretty e => Pretty (Located e) where
  ppr (L l e) = sep [char '{' <> ppr l <> char '}', ppr e]

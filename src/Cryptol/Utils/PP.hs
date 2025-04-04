-- |
-- Module      :  Cryptol.Utils.PP
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Utils.PP where

import           Cryptol.Utils.Fixity
import           Cryptol.Utils.Ident
import           Control.DeepSeq
import           Control.Monad (mplus)
import           Data.Maybe (fromMaybe)
import           Data.String (IsString(..))
import qualified Data.Text as T
import           Data.Void (Void)
import           GHC.Generics (Generic)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Util as PP
import qualified Prettyprinter.Render.String as PP

-- | How to pretty print things when evaluating
data PPOpts = PPOpts
  { useAscii      :: Bool
  , useBase       :: Int
  , useInfLength  :: Int
  , useFPBase     :: Int
  , useFPFormat   :: PPFloatFormat
  , useFieldOrder :: FieldOrder
  }
 deriving Show

asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)

data PPFloatFormat =
    FloatFixed Int PPFloatExp -- ^ Use this many significant digis
  | FloatFrac Int             -- ^ Show this many digits after floating point
  | FloatFree PPFloatExp      -- ^ Use the correct number of digits
 deriving Show

data PPFloatExp = ForceExponent -- ^ Always show an exponent
                | AutoExponent  -- ^ Only show exponent when needed
 deriving Show

data FieldOrder = DisplayOrder | CanonicalOrder
  deriving (Bounded, Enum, Eq, Ord, Read, Show)


defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5
                       , useFPBase = 16
                       , useFPFormat = FloatFree AutoExponent
                       , useFieldOrder = DisplayOrder
                       }


-- Name Displaying -------------------------------------------------------------

{- | How to display names, inspired by the GHC `Outputable` module.
Getting a value of 'Nothing' from the NameDisp function indicates
that the display has no opinion on how this name should be displayed,
and some other display should be tried out. -}
data NameDisp = EmptyNameDisp
              | NameDisp (OrigName -> Maybe NameFormat)
                deriving (Generic, NFData)

instance Show NameDisp where
  show _ = "<NameDisp>"

instance Semigroup NameDisp where
  NameDisp f    <> NameDisp g    = NameDisp (\n -> f n `mplus` g n)
  EmptyNameDisp <> EmptyNameDisp = EmptyNameDisp
  EmptyNameDisp <> x             = x
  x             <> _             = x

instance Monoid NameDisp where
  mempty = EmptyNameDisp
  mappend = (<>)

data NameFormat = UnQualified
                | Qualified !ModName
                | NotInScope
                  deriving (Show)

-- | Never qualify names from this module.
neverQualifyMod :: ModPath -> NameDisp
neverQualifyMod mn = NameDisp $ \n ->
  case ogSource n of
    FromDefinition | ogModule n == mn -> Just UnQualified
    _ -> Nothing

neverQualify :: NameDisp
neverQualify  = NameDisp $ \ _ -> Just UnQualified


-- | Compose two naming environments, preferring names from the left
-- environment.
extend :: NameDisp -> NameDisp -> NameDisp
extend  = mappend

-- | Get the format for a name.
getNameFormat :: OrigName -> NameDisp -> NameFormat
getNameFormat m (NameDisp f)  = fromMaybe NotInScope (f m)
getNameFormat _ EmptyNameDisp = NotInScope

-- | Produce a document in the context of the current 'NameDisp'.
withNameDisp :: (NameDisp -> Doc) -> Doc
withNameDisp k = withPPCfg (k . ppcfgNameDisp)

-- | Produce a document in the context of the current configuration.
withPPCfg :: (PPCfg -> Doc) -> Doc
withPPCfg k = Doc (\cfg -> runDocWith cfg (k cfg))

-- | Fix the way that names are displayed inside of a doc.
fixNameDisp :: NameDisp -> Doc -> Doc
fixNameDisp disp d =
  withPPCfg (\cfg -> fixPPCfg cfg { ppcfgNameDisp = disp } d)

-- | Fix the way that names are displayed inside of a doc.
fixPPCfg :: PPCfg -> Doc -> Doc
fixPPCfg cfg (Doc f) = Doc (\_ -> f cfg)

updPPCfg :: (PPCfg -> PPCfg) -> Doc -> Doc
updPPCfg f d = withPPCfg (\cfg -> fixPPCfg (f cfg) d)

debugShowUniques :: Doc -> Doc
debugShowUniques = updPPCfg \cfg -> cfg { ppcfgShowNameUniques = True }




-- Documents -------------------------------------------------------------------

data PPCfg = PPCfg
  { ppcfgNameDisp     :: NameDisp
  , ppcfgShowNameUniques :: Bool
  }

defaultPPCfg :: PPCfg
defaultPPCfg = PPCfg
  { ppcfgNameDisp = mempty
  , ppcfgShowNameUniques = False
  }

newtype Doc = Doc (PPCfg -> PP.Doc Void) deriving (Generic, NFData)

instance Semigroup Doc where
  (<>) = liftPP2 (<>)

instance Monoid Doc where
  mempty = liftPP mempty
  mappend = (<>)

runDocWith :: PPCfg -> Doc -> PP.Doc Void
runDocWith names (Doc f) = f names

runDoc :: NameDisp -> Doc -> PP.Doc Void
runDoc disp = runDocWith defaultPPCfg { ppcfgNameDisp = disp }

instance Show Doc where
  show d = PP.renderString (PP.layoutPretty opts (runDocWith defaultPPCfg d))
    where opts = PP.defaultLayoutOptions
                    { PP.layoutPageWidth = PP.AvailablePerLine 100 0.666 }

instance IsString Doc where
  fromString = text

renderOneLine :: Doc -> String
renderOneLine d = PP.renderString (PP.layoutPretty opts (runDocWith defaultPPCfg d))
  where
    opts = PP.LayoutOptions
      { PP.layoutPageWidth = PP.Unbounded
      }

class PP a where
  ppPrec :: Int -> a -> Doc

class PP a => PPName a where
  -- | Fixity information for infix operators
  ppNameFixity :: a -> Maybe Fixity

  -- | Print a name in prefix: @f a b@ or @(+) a b)@
  ppPrefixName :: a -> Doc

  -- | Print a name as an infix operator: @a + b@
  ppInfixName  :: a -> Doc

instance PPName ModName where
  ppNameFixity _ = Nothing
  ppPrefixName   = pp
  ppInfixName    = pp

pp :: PP a => a -> Doc
pp = ppPrec 0

pretty :: PP a => a -> String
pretty  = show . pp

optParens :: Bool -> Doc -> Doc
optParens b body | b         = nest 1 (parens body)
                 | otherwise = body


-- | Information about an infix expression of some sort.
data Infix op thing = Infix
  { ieOp     :: op       -- ^ operator
  , ieLeft   :: thing    -- ^ left argument
  , ieRight  :: thing    -- ^ right argument
  , ieFixity :: Fixity   -- ^ operator fixity
  }

-- | Pretty print an infix expression of some sort.
ppInfix :: (PP thing, PP op)
        => Int            -- ^ Non-infix leaves are printed with this precedence
        -> (thing -> Maybe (Infix op thing))
                          -- ^ pattern to check if sub-thing is also infix
        -> Infix op thing -- ^ Pretty print this infix expression
        -> Doc
ppInfix lp isInfix expr =
  sep [ ppSub wrapL (ieLeft expr) <+> pp (ieOp expr)
      , ppSub wrapR (ieRight expr) ]
  where
    wrapL f = compareFixity f (ieFixity expr) /= FCLeft
    wrapR f = compareFixity (ieFixity expr) f /= FCRight

    ppSub w e
      | Just e1 <- isInfix e = optParens (w (ieFixity e1)) (ppInfix lp isInfix e1)
    ppSub _ e                = ppPrec lp e



-- | Display a numeric value as an ordinal (e.g., 2nd)
ordinal :: (Integral a, Show a, Eq a) => a -> Doc
ordinal x = text (show x) <.> text (ordSuffix x)

-- | The suffix to use when displaying a number as an oridinal
ordSuffix :: (Integral a, Eq a) => a -> String
ordSuffix n0 =
  case n `mod` 10 of
    1 | notTeen -> "st"
    2 | notTeen -> "nd"
    3 | notTeen -> "rd"
    _ -> "th"

  where
  n       = abs n0
  m       = n `mod` 100
  notTeen = m < 11 || m > 19


-- Wrapped Combinators ---------------------------------------------------------

liftPP :: PP.Doc Void -> Doc
liftPP d = Doc (const d)

liftPP1 :: (PP.Doc Void -> PP.Doc Void) -> Doc -> Doc
liftPP1 f (Doc d) = Doc (\env -> f (d env))

liftPP2 :: (PP.Doc Void -> PP.Doc Void -> PP.Doc Void) -> (Doc -> Doc -> Doc)
liftPP2 f (Doc a) (Doc b) = Doc (\e -> f (a e) (b e))

liftSep :: ([PP.Doc Void] -> PP.Doc Void) -> ([Doc] -> Doc)
liftSep f ds = Doc (\e -> f [ d e | Doc d <- ds ])

reflow :: T.Text -> Doc
reflow x = liftPP (PP.reflow x)

infixl 6 <.>, <+>, </>

(<.>) :: Doc -> Doc -> Doc
(<.>)  = liftPP2 (PP.<>)

(<+>) :: Doc -> Doc -> Doc
(<+>)  = liftPP2 (PP.<+>)

(</>) :: Doc -> Doc -> Doc
Doc x </> Doc y = Doc (\e -> x e <> PP.softline <> y e)

infixl 5 $$

($$) :: Doc -> Doc -> Doc
($$) x y = vsep [x,y]

sep :: [Doc] -> Doc
sep  = liftSep PP.sep

fsep :: [Doc] -> Doc
fsep  = liftSep PP.fillSep

hsep :: [Doc] -> Doc
hsep  = liftSep PP.hsep

hcat :: [Doc] -> Doc
hcat  = liftSep PP.hcat

vcat :: [Doc] -> Doc
vcat  = liftSep PP.vcat

vsep :: [Doc] -> Doc
vsep  = liftSep PP.vsep

group :: Doc -> Doc
group = liftPP1 PP.group

-- NB, this is the semantics of "hang" as defined
--  by the HugesPJ printer, not the "hang" from prettyprinter,
--  which is subtly different.
hang :: Doc -> Int -> Doc -> Doc
hang (Doc p) i (Doc q) = Doc (\e -> PP.hang i (PP.vsep [p e, q e]))

nest :: Int -> Doc -> Doc
nest n = liftPP1 (PP.nest n)

indent :: Int -> Doc -> Doc
indent n = liftPP1 (PP.indent n)

align :: Doc -> Doc
align = liftPP1 PP.align

parens :: Doc -> Doc
parens  = liftPP1 PP.parens

braces :: Doc -> Doc
braces  = liftPP1 PP.braces

brackets :: Doc -> Doc
brackets  = liftPP1 PP.brackets

quotes :: Doc -> Doc
quotes  = liftPP1 PP.squotes

commaSep :: [Doc] -> Doc
commaSep xs = Doc (\e -> PP.sep (PP.punctuate PP.comma [ d e | Doc d <- xs ]))

-- | Print a comma-separated list. Lay out each item on a single line
-- if it will fit. If an item requires multiple lines, then start it
-- on its own line.
commaSepFill :: [Doc] -> Doc
commaSepFill xs = Doc (\e -> fillSep (PP.punctuate PP.comma [ d e | Doc d <- xs ]))
  where
    fillSep [] = mempty
    fillSep (d0 : ds) = foldl (\a d -> a <> PP.group (PP.line <> d)) d0 ds

ppList :: [Doc] -> Doc
ppList xs = group (nest 1 (brackets (commaSepFill xs)))

ppTuple :: [Doc] -> Doc
ppTuple xs = group (nest 1 (parens (commaSep xs)))

ppRecord :: [Doc] -> Doc
ppRecord xs = group (nest 1 (braces (commaSep xs)))

backticks :: Doc -> Doc
backticks d = hcat [ "`", d, "`" ]

text :: String -> Doc
text s = liftPP (PP.pretty s)

char :: Char -> Doc
char c = liftPP (PP.pretty c)

integer :: Integer -> Doc
integer i = liftPP (PP.pretty i)

int :: Int -> Doc
int i = liftPP (PP.pretty i)

comma :: Doc
comma  = liftPP PP.comma

colon :: Doc
colon  = liftPP PP.colon

pipe :: Doc
pipe = liftPP PP.pipe


instance PP T.Text where
  ppPrec _ str = text (T.unpack str)

instance PP Ident where
  ppPrec _ i = text (T.unpack (identText i))

instance PP ModName where
  ppPrec _   = text . T.unpack . modNameToText

instance PP Assoc where
  ppPrec _ LeftAssoc  = text "left-associative"
  ppPrec _ RightAssoc = text "right-associative"
  ppPrec _ NonAssoc   = text "non-associative"

instance PP Fixity where
  ppPrec _ (Fixity assoc level) =
    text "precedence" <+> int level <.> comma <+> pp assoc

instance PP ModPath where
  ppPrec _ p =
    case p of
      TopModule m -> pp m
      Nested q t  -> pp q <.> "::" <.> pp t

instance PP OrigName where
  ppPrec _ og =
    withNameDisp $ \disp ->
      case getNameFormat og disp of
        UnQualified -> pp (ogName og)
        Qualified m -> ppQual (TopModule m) (pp (ogName og))
        NotInScope  -> ppQual (ogModule og)
                       case ogFromParam og of
                         Just x | not (isAnonIfaceModIdnet x) -> pp x <.> "::" <.> pp (ogName og)
                         _ -> pp (ogName og)
    where
    ppQual mo x =
      case mo of
        TopModule m
          | m == exprModName -> x
          | otherwise -> pp m <.> "::" <.> x
        Nested m y -> ppQual m (pp y <.> "::" <.> x)

instance PP Namespace where
  ppPrec _ ns =
    case ns of
      NSValue     -> "/*value*/"
      NSConstructor -> "/*constructor*/"
      NSType      -> "/*type*/"
      NSModule    -> "/*module*/"

instance PP PrimIdent where
  ppPrec _ (PrimIdent m t) = pp m <.> "::" <.> text (T.unpack t)

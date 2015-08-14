-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Utils.PP where

import           Cryptol.ModuleSystem.Name

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Monoid as M
import           Data.String (IsString(..))
import qualified Text.PrettyPrint as PJ

import GHC.Generics (Generic)
import Control.DeepSeq

-- | How to display names.
newtype NameEnv = NameEnv (Map QName NameInfo)
                  deriving (Show)

data NameInfo = NameInfo { niDisp  :: QName
                         , niInfix :: Bool
                         } deriving (Show)

mkNameEnv :: [(QName,NameInfo)] -> NameEnv
mkNameEnv  = NameEnv . Map.fromList

-- | Compose two naming environments.
extend :: NameEnv -> NameEnv -> NameEnv
extend (NameEnv l) (NameEnv r) = NameEnv (lkp `fmap` l)
  where
  lkp ni = Map.findWithDefault ni (niDisp ni) r

getNameInfo :: QName -> NameEnv -> NameInfo
getNameInfo n (NameEnv e) = Map.findWithDefault (NameInfo n False) n e

instance M.Monoid NameEnv where
  mempty                          = NameEnv Map.empty
  mappend (NameEnv a) (NameEnv b) = NameEnv (Map.union a b)

newtype Doc = Doc (NameEnv -> PJ.Doc) deriving (Generic)

instance NFData Doc

runDoc :: NameEnv -> Doc -> PJ.Doc
runDoc names (Doc f) = f names

instance Show Doc where
  show d = show (runDoc M.mempty d)

instance IsString Doc where
  fromString = text

render :: Doc -> String
render d = PJ.render (runDoc M.mempty d)

class PP a where
  ppPrec :: Int -> a -> Doc

pp :: PP a => a -> Doc
pp = ppPrec 0

pretty :: PP a => a -> String
pretty  = show . pp

optParens :: Bool -> Doc -> Doc
optParens b body | b         = parens body
                 | otherwise = body


-- | Information about associativity.
data Assoc = LeftAssoc | RightAssoc | NonAssoc
              deriving (Show,Eq,Generic)

instance NFData Assoc

-- | Information about an infix expression of some sort.
data Infix op thing = Infix
  { ieOp    :: op       -- ^ operator
  , ieLeft  :: thing    -- ^ left argument
  , ieRight :: thing    -- ^ right argumrnt
  , iePrec  :: Int      -- ^ operator precedence
  , ieAssoc :: Assoc    -- ^ operator associativity
  }

commaSep :: [Doc] -> Doc
commaSep = fsep . punctuate comma


-- | Pretty print an infix expression of some sort.
ppInfix :: (PP thing, PP op)
        => Int            -- ^ Non-infix leaves are printed with this precedence
        -> (thing -> Maybe (Infix op thing))
                          -- ^ pattern to check if sub-thing is also infix
        -> Infix op thing -- ^ Pretty print this infix expression
        -> Doc
ppInfix lp isInfix expr =
  sep [ ppSub (wrapSub LeftAssoc ) (ieLeft expr) <+> pp (ieOp expr)
      , ppSub (wrapSub RightAssoc) (ieRight expr) ]
  where
  wrapSub dir p = p < iePrec expr || p == iePrec expr && ieAssoc expr /= dir

  ppSub w e
    | Just e1 <- isInfix e = optParens (w (iePrec e1)) (ppInfix lp isInfix e1)
  ppSub _ e                = ppPrec lp e



-- | Display a numeric values as an ordinar (e.g., 2nd)
ordinal :: (Integral a, Show a, Eq a) => a -> Doc
ordinal x = text (show x) <> text (ordSuffix x)

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

liftPJ :: PJ.Doc -> Doc
liftPJ d = Doc (const d)

liftPJ1 :: (PJ.Doc -> PJ.Doc) -> Doc -> Doc
liftPJ1 f (Doc d) = Doc (\env -> f (d env))

liftPJ2 :: (PJ.Doc -> PJ.Doc -> PJ.Doc) -> (Doc -> Doc -> Doc)
liftPJ2 f (Doc a) (Doc b) = Doc (\e -> f (a e) (b e))

liftSep :: ([PJ.Doc] -> PJ.Doc) -> ([Doc] -> Doc)
liftSep f ds = Doc (\e -> f [ d e | Doc d <- ds ])

(<>) :: Doc -> Doc -> Doc
(<>)  = liftPJ2 (PJ.<>)

(<+>) :: Doc -> Doc -> Doc
(<+>)  = liftPJ2 (PJ.<+>)

($$) :: Doc -> Doc -> Doc
($$)  = liftPJ2 (PJ.$$)

sep :: [Doc] -> Doc
sep  = liftSep PJ.sep

fsep :: [Doc] -> Doc
fsep  = liftSep PJ.fsep

hsep :: [Doc] -> Doc
hsep  = liftSep PJ.hsep

hcat :: [Doc] -> Doc
hcat  = liftSep PJ.hcat

vcat :: [Doc] -> Doc
vcat  = liftSep PJ.vcat

hang :: Doc -> Int -> Doc -> Doc
hang (Doc p) i (Doc q) = Doc (\e -> PJ.hang (p e) i (q e))

nest :: Int -> Doc -> Doc
nest n = liftPJ1 (PJ.nest n)

parens :: Doc -> Doc
parens  = liftPJ1 PJ.parens

braces :: Doc -> Doc
braces  = liftPJ1 PJ.braces

brackets :: Doc -> Doc
brackets  = liftPJ1 PJ.brackets

quotes :: Doc -> Doc
quotes  = liftPJ1 PJ.quotes

punctuate :: Doc -> [Doc] -> [Doc]
punctuate p = go
  where
  go (d:ds) | null ds   = [d]
            | otherwise = d <> p : go ds
  go []                 = []

text :: String -> Doc
text s = liftPJ (PJ.text s)

char :: Char -> Doc
char c = liftPJ (PJ.char c)

integer :: Integer -> Doc
integer i = liftPJ (PJ.integer i)

int :: Int -> Doc
int i = liftPJ (PJ.int i)

comma :: Doc
comma  = liftPJ PJ.comma

empty :: Doc
empty  = liftPJ PJ.empty

colon :: Doc
colon  = liftPJ PJ.colon


-- Names -----------------------------------------------------------------------

withNameEnv :: (NameEnv -> Doc) -> Doc
withNameEnv f = Doc (\e -> runDoc e (f e))

fixNameEnv :: NameEnv -> Doc -> Doc
fixNameEnv env (Doc f) = Doc (\_ -> f env)

instance PP ModName where
  ppPrec _ (ModName ns) = hcat (punctuate (text "::") (map text ns))

instance PP QName where
  ppPrec _ qn = withNameEnv $ \ names ->
    let NameInfo (QName mb n) isInfix = getNameInfo qn names
        mbNs = maybe empty (\ mn -> pp mn <> text "::") mb
     in optParens isInfix (mbNs <> pp n)

instance PP Name where
  ppPrec _ (Name x)       = text x
  -- XXX: This may clash with user-specified names.
  ppPrec _ (NewName p x)  = text "__" <> passName p <> int x

-- | Pretty-print the qualified name as-is; don't consult the environment.
ppQName :: QName -> Doc
ppQName (QName mb n) = maybe empty (\ mn -> pp mn <> text "::") mb <> pp n

passName :: Pass -> Doc
passName pass =
  case pass of
    NoPat       -> text "p"
    MonoValues  -> text "mv"


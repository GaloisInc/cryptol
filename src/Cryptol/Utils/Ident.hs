-- |
-- Module      :  Cryptol.Utils.Ident
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveGeneric, OverloadedStrings #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE Safe #-}

module Cryptol.Utils.Ident
  ( -- * Module names
    ModPath(..)
  , apPathRoot
  , modPathCommon
  , topModuleFor
  , modPathSplit

  , ModName
  , modNameToText
  , textToModName
  , modNameChunks
  , packModName
  , preludeName
  , preludeReferenceName
  , floatName
  , suiteBName
  , arrayName
  , primeECName
  , interactiveName
  , noModuleName
  , exprModName

  , isParamInstModName
  , paramInstModName
  , notParamInstModName

    -- * Identifiers
  , Ident
  , packIdent
  , packInfix
  , unpackIdent
  , mkIdent
  , mkInfix
  , isInfixIdent
  , nullIdent
  , identText
  , modParamIdent

    -- * Namespaces
  , Namespace(..)
  , allNamespaces

    -- * Original names
  , OrigName(..)

    -- * Identifiers for primitives
  , PrimIdent(..)
  , prelPrim
  , floatPrim
  , arrayPrim
  , suiteBPrim
  , primeECPrim
  ) where

import           Control.DeepSeq (NFData)
import           Data.Char (isSpace)
import           Data.List (unfoldr)
import qualified Data.Text as T
import           Data.String (IsString(..))
import           GHC.Generics (Generic)


--------------------------------------------------------------------------------

-- | Namespaces for names
data Namespace = NSValue | NSType | NSModule
  deriving (Generic,Show,NFData,Eq,Ord,Enum,Bounded)

allNamespaces :: [Namespace]
allNamespaces = [ minBound .. maxBound ]

-- | Idnetifies a possibly nested module
data ModPath  = TopModule ModName
              | Nested ModPath Ident
                deriving (Eq,Ord,Show,Generic,NFData)

apPathRoot :: (ModName -> ModName) -> ModPath -> ModPath
apPathRoot f path =
  case path of
    TopModule m -> TopModule (f m)
    Nested p q  -> Nested (apPathRoot f p) q

topModuleFor :: ModPath -> ModName
topModuleFor m =
  case m of
    TopModule x -> x
    Nested p _ -> topModuleFor p

-- | Compute a common prefix between two module paths, if any.
-- This is basically "anti-unification" of the two paths, where we
-- compute the longest common prefix, and the remaining differences for
-- each module.
modPathCommon :: ModPath -> ModPath -> Maybe (ModPath, [Ident], [Ident])
modPathCommon p1 p2
  | top1 == top2 = Just (findCommon (TopModule top1) as bs)
  | otherwise    = Nothing
  where
  (top1,as) = modPathSplit p1
  (top2,bs) = modPathSplit p2

  findCommon com xs ys =
    case (xs,ys) of
      (x:xs',y:ys') | x == y -> findCommon (Nested com x) xs' ys'
      _                      -> (com, xs, ys)

modPathSplit :: ModPath -> (ModName, [Ident])
modPathSplit p0 = (top,reverse xs)
  where
  (top,xs) = go p0
  go p =
    case p of
      TopModule a -> (a, [])
      Nested b i  -> (a, i:bs)
        where (a,bs) = go b




--------------------------------------------------------------------------------
-- | Top-level Module names are just text.
data ModName = ModName T.Text
  deriving (Eq,Ord,Show,Generic)

instance NFData ModName

modNameToText :: ModName -> T.Text
modNameToText (ModName x) = x

textToModName :: T.Text -> ModName
textToModName = ModName

modNameChunks :: ModName -> [String]
modNameChunks  = unfoldr step . modNameToText . notParamInstModName
  where
  step str
    | T.null str = Nothing
    | otherwise  = case T.breakOn modSep str of
                     (a,b) -> Just (T.unpack a,T.drop (T.length modSep) b)

isParamInstModName :: ModName -> Bool
isParamInstModName (ModName x) = modInstPref `T.isPrefixOf` x

-- | Convert a parameterized module's name to the name of the module
-- containing the same definitions but with explicit parameters on each
-- definition.
paramInstModName :: ModName -> ModName
paramInstModName (ModName x)
  | modInstPref `T.isPrefixOf` x = ModName x
  | otherwise = ModName (T.append modInstPref x)


notParamInstModName :: ModName -> ModName
notParamInstModName (ModName x)
  | modInstPref `T.isPrefixOf` x = ModName (T.drop (T.length modInstPref) x)
  | otherwise = ModName x


packModName :: [T.Text] -> ModName
packModName strs = textToModName (T.intercalate modSep (map trim strs))
  where
  -- trim space off of the start and end of the string
  trim str = T.dropWhile isSpace (T.dropWhileEnd isSpace str)

modSep :: T.Text
modSep  = "::"

modInstPref :: T.Text
modInstPref = "`"


preludeName :: ModName
preludeName  = packModName ["Cryptol"]

preludeReferenceName :: ModName
preludeReferenceName = packModName ["Cryptol","Reference"]

floatName :: ModName
floatName = packModName ["Float"]

arrayName :: ModName
arrayName  = packModName ["Array"]

suiteBName :: ModName
suiteBName = packModName ["SuiteB"]

primeECName :: ModName
primeECName = packModName ["PrimeEC"]

interactiveName :: ModName
interactiveName  = packModName ["<interactive>"]

noModuleName :: ModName
noModuleName = packModName ["<none>"]

exprModName :: ModName
exprModName = packModName ["<expr>"]


--------------------------------------------------------------------------------
-- | Identifies an entitiy
data OrigName = OrigName
  { ogNamespace :: Namespace
  , ogModule    :: ModPath
  , ogName      :: Ident
  } deriving (Eq,Ord,Show,Generic,NFData)


--------------------------------------------------------------------------------

-- | Identifiers, along with a flag that indicates whether or not they're infix
-- operators. The boolean is present just as cached information from the lexer,
-- and never used during comparisons.
data Ident = Ident Bool T.Text
             deriving (Show,Generic)

instance Eq Ident where
  a == b = compare a b == EQ
  a /= b = compare a b /= EQ

instance Ord Ident where
  compare (Ident _ i1) (Ident _ i2) = compare i1 i2

instance IsString Ident where
  fromString str = mkIdent (T.pack str)

instance NFData Ident

packIdent :: String -> Ident
packIdent  = mkIdent . T.pack

packInfix :: String -> Ident
packInfix  = mkInfix . T.pack

unpackIdent :: Ident -> String
unpackIdent  = T.unpack . identText

mkIdent :: T.Text -> Ident
mkIdent  = Ident False

mkInfix :: T.Text -> Ident
mkInfix  = Ident True

isInfixIdent :: Ident -> Bool
isInfixIdent (Ident b _) = b

nullIdent :: Ident -> Bool
nullIdent (Ident _ t) = T.null t

identText :: Ident -> T.Text
identText (Ident _ t) = t

modParamIdent :: Ident -> Ident
modParamIdent (Ident x t) = Ident x (T.append (T.pack "module parameter ") t)


--------------------------------------------------------------------------------

{- | A way to identify primitives: we used to use just 'Ident', but this
isn't good anymore as now we have primitives in multiple modules.
This is used as a key when we need to lookup details about a specific
primitive.  Also, this is intended to mostly be used internally, so
we don't store the fixity flag of the `Ident` -}
data PrimIdent = PrimIdent ModName T.Text
  deriving (Eq,Ord,Show,Generic)

-- | A shortcut to make (non-infix) primitives in the prelude.
prelPrim :: T.Text -> PrimIdent
prelPrim = PrimIdent preludeName

floatPrim :: T.Text -> PrimIdent
floatPrim = PrimIdent floatName

suiteBPrim :: T.Text -> PrimIdent
suiteBPrim = PrimIdent suiteBName

primeECPrim :: T.Text -> PrimIdent
primeECPrim = PrimIdent primeECName

arrayPrim :: T.Text -> PrimIdent
arrayPrim = PrimIdent arrayName

instance NFData PrimIdent

-- |
-- Module      :  Cryptol.Utils.Ident
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveGeneric, OverloadedStrings #-}

module Cryptol.Utils.Ident
  ( -- * Module names
    ModName
  , modNameToText
  , textToModName
  , modNameChunks
  , packModName
  , preludeName
  , floatName
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
  , floatPrimIdent

  ) where

import           Control.DeepSeq (NFData)
import           Data.Char (isSpace)
import           Data.List (unfoldr)
import qualified Data.Text as T
import           Data.String (IsString(..))
import           GHC.Generics (Generic)


-- | Module names are just text.
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

floatName :: ModName
floatName = packModName ["Float"]


interactiveName :: ModName
interactiveName  = packModName ["<interactive>"]

noModuleName :: ModName
noModuleName = packModName ["<none>"]

exprModName :: ModName
exprModName = packModName ["<expr>"]


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

floatPrimIdent :: T.Text -> Ident
floatPrimIdent t = mkIdent ("Float::" <> t)


-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveGeneric #-}

module Cryptol.Utils.Ident where

import           Control.DeepSeq (NFData)
import           Data.Char (isSpace)
import           Data.List (unfoldr)
import qualified Data.Text as T
import           Data.String (IsString(..))
import           GHC.Generics (Generic)


-- | Module names are just text.
type ModName = T.Text

unpackModName :: ModName -> [String]
unpackModName  = unfoldr step
  where
  step str
    | T.null str = Nothing
    | otherwise  = case T.breakOn modSep str of
                     (a,b) -> Just (T.unpack a,T.drop (T.length modSep) b)

packModName :: [String] -> ModName
packModName strs = T.intercalate modSep (map (trim . T.pack) strs)
  where
  -- trim space off of the start and end of the string
  trim str = T.dropWhile isSpace (T.dropWhileEnd isSpace str)

modSep :: T.Text
modSep  = T.pack "::"

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


-- Frequently Used Names -------------------------------------------------------

preludeName :: ModName
preludeName  = packModName ["Cryptol"]

preludeExtrasName :: ModName
preludeExtrasName = packModName ["Cryptol", "Extras"]

interactiveName :: ModName
interactiveName  = packModName ["<interactive>"]

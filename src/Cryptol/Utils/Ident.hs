{-# LANGUAGE DeriveGeneric #-}

module Cryptol.Utils.Ident where

import           Control.DeepSeq (NFData)
import qualified Data.Text as T
import           Data.String (IsString(..))
import           GHC.Generics (Generic)


-- | Module names are just text.
type ModName = T.Text

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
preludeName  = T.pack "Cryptol"

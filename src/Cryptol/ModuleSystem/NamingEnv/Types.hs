{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.ModuleSystem.NamingEnv.Types where

import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map

import           Control.DeepSeq            (NFData)
import           GHC.Generics               (Generic)

import           Cryptol.ModuleSystem.Names
import           Cryptol.Parser.Name
import           Cryptol.Utils.Ident
import           Cryptol.Utils.PP

-- | The 'NamingEnv' is used by the renamer to determine what
-- identifiers refer to.
newtype NamingEnv = NamingEnv (Map Namespace (Map PName Names))
  deriving (Show,Generic,NFData)

instance Monoid NamingEnv where
  mempty = NamingEnv Map.empty
  {-# INLINE mempty #-}

instance Semigroup NamingEnv where
  NamingEnv l <> NamingEnv r =
    NamingEnv (Map.unionWith (Map.unionWith (<>)) l r)

instance PP NamingEnv where
  ppPrec _ (NamingEnv mps)   = vcat $ map ppNS $ Map.toList mps
    where ppNS (ns,xs) = nest 2 (vcat (pp ns : map ppNm (Map.toList xs)))
          ppNm (x,as)  = pp x <+> "->" <+> commaSep (map pp (namesToList as))

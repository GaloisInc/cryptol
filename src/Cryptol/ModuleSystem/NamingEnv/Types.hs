{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.ModuleSystem.NamingEnv.Types where

import           Data.List(partition)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import qualified Data.Set                   as Set

import           Control.DeepSeq            (NFData)
import           GHC.Generics               (Generic)

import           Cryptol.ModuleSystem.Name
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
  ppPrec _ (NamingEnv mps) = vcat $ map ppNS $ Map.toList mps
    where
    isPrel x =
      case nameModPathMaybe x of
        Nothing -> False
        Just p -> topModuleFor p == preludeName
    
    skip (x,as) (count, defs) =
      let (ps,qs) = partition isPrel (namesToList as)
      in ( count + length ps
         , if null qs then defs else (x,namesFromSet (Set.fromList qs)) : defs
      )

    ppNS (ns,xs) =
      withPPCfg (\cfg ->
        let (skipped,shown)
              | not (ppcfgHidePreludeNames cfg) = (0,Map.toList xs)
              | otherwise = foldr skip (0,[]) (Map.toList xs)
            skippedDoc = if skipped > 0 then "Skipped" <+> int skipped <+> "names from `Cryptol" else mempty
        in nest 2 (vcat (pp ns : skippedDoc : map ppNm shown))
        )
    ppNm (x,as)  = pp x <+> "->" <+> commaSep (map pp (namesToList as))

-- | Move names in the constructor namespace to the value namespace.
-- This is handy when checking for ambiguities.
consToValues :: NamingEnv -> NamingEnv
consToValues (NamingEnv mps) =
  NamingEnv $
  case Map.updateLookupWithKey (\_ _ -> Nothing) NSConstructor mps of
    (Nothing, mp1) -> mp1
    (Just conMap, mp1) -> Map.insertWith (Map.unionWith (<>)) NSValue conMap mp1

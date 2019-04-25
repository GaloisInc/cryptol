{-# LANGUAGE DeriveGeneric #-}
module Cryptol.ModuleSystem.Exports where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Foldable(fold)
import Data.Semigroup (Semigroup(..))
import Control.DeepSeq(NFData)
import GHC.Generics (Generic)

import Cryptol.Parser.AST
import Cryptol.Parser.Names

modExports :: Ord name => Module name -> ExportSpec name
modExports m = fold (concat [ exportedNames d | d <- mDecls m ])
  where
  names by td = [ td { tlValue = thing n } | n <- fst (by (tlValue td)) ]

  exportedNames (Decl td) = map exportBind  (names  namesD td)
                         ++ map exportType (names tnamesD td)
  exportedNames (DPrimType t) = [ exportType (thing . primTName <$> t) ]
  exportedNames (TDNewtype nt) = map exportType (names tnamesNT nt)
  exportedNames (Include {})  = []
  exportedNames (DParameterFun {}) = []
  exportedNames (DParameterType {}) = []
  exportedNames (DParameterConstraint {}) = []



data ExportSpec name = ExportSpec { eTypes  :: Set name
                                  , eBinds  :: Set name
                                  } deriving (Show, Generic)

instance NFData name => NFData (ExportSpec name)

instance Ord name => Semigroup (ExportSpec name) where
  l <> r = ExportSpec { eTypes = eTypes l <> eTypes r
                      , eBinds = eBinds l <> eBinds  r
                      }

instance Ord name => Monoid (ExportSpec name) where
  mempty  = ExportSpec { eTypes = mempty, eBinds = mempty }
  mappend = (<>)

-- | Add a binding name to the export list, if it should be exported.
exportBind :: Ord name => TopLevel name -> ExportSpec name
exportBind n
  | tlExport n == Public = mempty { eBinds = Set.singleton (tlValue n) }
  | otherwise            = mempty

-- | Add a type synonym name to the export list, if it should be exported.
exportType :: Ord name => TopLevel name -> ExportSpec name
exportType n
  | tlExport n == Public = mempty { eTypes = Set.singleton (tlValue n) }
  | otherwise            = mempty

-- | Check to see if a binding is exported.
isExportedBind :: Ord name => name -> ExportSpec name -> Bool
isExportedBind n = Set.member n . eBinds

-- | Check to see if a type synonym is exported.
isExportedType :: Ord name => name -> ExportSpec name -> Bool
isExportedType n = Set.member n . eTypes




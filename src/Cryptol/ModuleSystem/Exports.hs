{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE Safe #-}
module Cryptol.ModuleSystem.Exports where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Foldable(fold)
import Control.DeepSeq(NFData)
import GHC.Generics (Generic)

import Cryptol.Parser.AST
import Cryptol.Parser.Names(namesD,tnamesD,tnamesNT)
import Cryptol.ModuleSystem.Name

modExports :: Ord name => ModuleG mname name -> ExportSpec name
modExports m = fold (concat [ exportedNames d | d <- mDecls m ])


exportedNames :: Ord name => TopDecl name -> [ExportSpec name]
exportedNames (Decl td) = map exportBind  (names namesD td)
                       ++ map exportType (names tnamesD td)
exportedNames (DPrimType t) = [ exportType (thing . primTName <$> t) ]
exportedNames (TDNewtype nt) = map exportType (names tnamesNT nt)
exportedNames (Include {})  = []
exportedNames (DImport {}) = []
exportedNames (DParameterFun {}) = []
exportedNames (DParameterType {}) = []
exportedNames (DParameterConstraint {}) = []
exportedNames (DModule nested) =
  case tlValue nested of
    NestedModule x ->
      [exportName NSModule nested { tlValue = thing (mName x) }]

names :: (a -> ([Located a'], b)) -> TopLevel a -> [TopLevel a']
names by td = [ td { tlValue = thing n } | n <- fst (by (tlValue td)) ]


newtype ExportSpec name = ExportSpec (Map Namespace (Set name))
                                        deriving (Show, Generic)

instance NFData name => NFData (ExportSpec name)

instance Ord name => Semigroup (ExportSpec name) where
  ExportSpec l <> ExportSpec r = ExportSpec (Map.unionWith Set.union l r)

instance Ord name => Monoid (ExportSpec name) where
  mempty  = ExportSpec Map.empty

exportName :: Ord name => Namespace -> TopLevel name -> ExportSpec name
exportName ns n
  | tlExport n == Public = ExportSpec
                         $ Map.singleton ns
                         $ Set.singleton (tlValue n)
  | otherwise = mempty

exported :: Namespace -> ExportSpec name -> Set name
exported ns (ExportSpec mp) = Map.findWithDefault Set.empty ns mp

-- | Add a binding name to the export list, if it should be exported.
exportBind :: Ord name => TopLevel name -> ExportSpec name
exportBind = exportName NSValue

-- | Add a type synonym name to the export list, if it should be exported.
exportType :: Ord name => TopLevel name -> ExportSpec name
exportType = exportName NSType



isExported :: Ord name => Namespace -> name -> ExportSpec name -> Bool
isExported ns x (ExportSpec s) =
  case Map.lookup ns s of
    Nothing -> False
    Just mp -> Set.member x mp

-- | Check to see if a binding is exported.
isExportedBind :: Ord name => name -> ExportSpec name -> Bool
isExportedBind = isExported NSValue

-- | Check to see if a type synonym is exported.
isExportedType :: Ord name => name -> ExportSpec name -> Bool
isExportedType = isExported NSType

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.Names
  ( visibleNames
  , visibleNamesDescr
  ) where

import qualified Argo.Doc as Doc
import qualified Data.Aeson as JSON
import Data.Aeson ((.=))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (unpack)

import Cryptol.Parser.Name (PName(..))
import Cryptol.ModuleSystem.Env (ModContext(..), ModuleEnv(..), DynamicEnv(..), focusedEnv)
import Cryptol.ModuleSystem.Interface (IfaceDecl(..), IfaceDecls(..))
import Cryptol.ModuleSystem.Name (Name)
import Cryptol.ModuleSystem.NamingEnv (NamingEnv(..), lookupValNames, shadowing)
import Cryptol.TypeCheck.Type (Schema(..))
import Cryptol.Utils.PP (pp)

import CryptolServer
import CryptolServer.Data.Type

data VisibleNamesParams = VisibleNamesParams

instance JSON.FromJSON VisibleNamesParams where
  parseJSON _ = pure VisibleNamesParams

instance Doc.DescribedParams VisibleNamesParams where
  parameterFieldDescription = []

visibleNamesDescr :: Doc.Block
visibleNamesDescr =
  Doc.Paragraph [Doc.Text "List the currently visible (i.e., in scope) names."]

visibleNames :: VisibleNamesParams -> CryptolMethod [NameInfo]
visibleNames _ =
  do me <- getModuleEnv
     let DEnv { deNames = dyNames } = meDynEnv me
     let ModContext { mctxDecls = fDecls, mctxNames = fNames} = focusedEnv me
     let inScope = Map.keys (neExprs $ dyNames `shadowing` fNames)
     return $ concatMap (getInfo fNames (ifDecls fDecls)) inScope

getInfo :: NamingEnv -> Map Name IfaceDecl -> PName -> [NameInfo]
getInfo rnEnv info n' =
  [ case Map.lookup n info of
       Nothing -> error $ "Name not found, but should have been: " ++ show n
       Just i ->
         let ty = ifDeclSig i
             nameDocs = ifDeclDoc i
         in NameInfo (show (pp n')) (show (pp ty)) ty (unpack <$> nameDocs)
  | n <- lookupValNames n' rnEnv
  ]

data NameInfo =
  NameInfo
  { name     :: String
  , typeSig  :: String
  , schema   :: Schema
  , nameDocs :: Maybe String
  }

instance JSON.ToJSON NameInfo where
  toJSON (NameInfo{name, typeSig, schema, nameDocs}) =
    JSON.object $
    [ "name" .= name
    , "type string" .= typeSig
    , "type" .= JSON.toJSON (JSONSchema schema)
    ] ++
    maybe [] (\d -> ["documentation" .= d]) nameDocs

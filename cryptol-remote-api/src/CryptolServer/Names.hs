{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
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
import Data.Maybe(maybeToList)
import Data.Typeable (Proxy(..), typeRep)

import Cryptol.Parser.Name (PName(..))
import Cryptol.ModuleSystem.Env (ModContext(..), ModuleEnv(..), DynamicEnv(..), focusedEnv)
import Cryptol.ModuleSystem.Interface (IfaceDecl(..), IfaceDecls(..))
import Cryptol.ModuleSystem.Name (Name)
import Cryptol.ModuleSystem.NamingEnv
                  (NamingEnv, namespaceMap, lookupNS, shadowing)
import Cryptol.ModuleSystem.Names(namesToList)
import Cryptol.TypeCheck.Type (Schema(..))
import Cryptol.Utils.PP (pp)
import Cryptol.Utils.Ident(Namespace(..))

import CryptolServer
import CryptolServer.Data.Type

data VisibleNamesParams = VisibleNamesParams

instance JSON.FromJSON VisibleNamesParams where
  parseJSON _ = pure VisibleNamesParams

instance Doc.DescribedMethod VisibleNamesParams [NameInfo] where
  parameterFieldDescription = []

  resultFieldDescription =
    [ ("name",
      Doc.Paragraph [Doc.Text "A human-readable representation of the name"])
    , ("type string",
      Doc.Paragraph [Doc.Text "A human-readable representation of the name's type schema"])
    , ("type",
      Doc.Paragraph [ Doc.Text " A"
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @JSONSchema))) "JSON Cryptol type"
                    ])
    , ("documentation",
      Doc.Paragraph [Doc.Text "An optional field containing documentation string for the name, if it is documented"])
    ]

visibleNamesDescr :: Doc.Block
visibleNamesDescr =
  Doc.Paragraph [Doc.Text "List the currently visible (i.e., in scope) names."]

visibleNames :: VisibleNamesParams -> CryptolCommand [NameInfo]
visibleNames _ =
  do me <- getModuleEnv
     let DEnv { deNames = dyNames } = meDynEnv me
     let ModContext { mctxDecls = fDecls, mctxNames = fNames} = focusedEnv me
     let inScope = Map.keys (namespaceMap NSValue $ dyNames `shadowing` fNames)
     return $ concatMap (getInfo fNames (ifDecls fDecls)) inScope

getInfo :: NamingEnv -> Map Name IfaceDecl -> PName -> [NameInfo]
getInfo rnEnv info n' =
  [ case Map.lookup n info of
       Nothing -> error $ "Name not found, but should have been: " ++ show n
       Just i ->
         let ty = ifDeclSig i
             nameDocs = ifDeclDoc i
         in NameInfo (show (pp n')) (show (pp ty)) ty (unpack <$> nameDocs)
  | ns <- maybeToList (lookupNS NSValue n' rnEnv), n <- namesToList ns
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

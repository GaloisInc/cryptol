{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
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
import Data.Typeable (Proxy(..), typeRep)
import Data.Maybe (fromMaybe)

import Cryptol.Parser.Name (PName(..))
import Cryptol.ModuleSystem.Env (ModContext(..), ModuleEnv(..), DynamicEnv(..), focusedEnv)
import Cryptol.ModuleSystem.Interface (IfaceDecl(..), IfaceDecls(..))
import Cryptol.ModuleSystem.Name (Name)
import qualified Cryptol.ModuleSystem.Name as N (nameInfo, NameInfo(Declared))
import Cryptol.ModuleSystem.NamingEnv
                  (NamingEnv, namespaceMap, lookupValNames, shadowing)
import Cryptol.TypeCheck.Type (Schema(..))
import Cryptol.Utils.Fixity(Fixity(..), defaultFixity)
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
    , ("module",
      Doc.Paragraph [Doc.Text "A human-readable representation of the module from which the name originates"])
    , ("infix",
      Doc.Paragraph [Doc.Text "An optional field which is present and True iff the name is an infix operator"])
    , ("infix associativity",
      Doc.Paragraph [ Doc.Text "An optional field containing one of the strings \"left-associative\", "
                    , Doc.Text "\"right-associative\", or \"non-associative\", if the name is an infix operator"])
    , ("infix level",
      Doc.Paragraph [ Doc.Text "An optional field containing the name's precedence level, if the name is an infix operator"])
    , ("pragmas",
      Doc.Paragraph [Doc.Text "An optional field containing a list of the name's pragmas (e.g. \"property\"), if it has any"])
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
       Just (IfaceDecl _ ty prags ifx fx nameDocs) ->
         let fxy = if not ifx then Nothing else case fromMaybe defaultFixity fx of
                    Fixity assoc lvl -> Just (show (pp assoc), lvl)
         in NameInfo (show (pp n')) (show (pp ty)) ty (show (pp m))
                     fxy (show . pp <$> prags) (unpack <$> nameDocs)
  | n <- lookupValNames n' rnEnv
  , N.Declared m _ <- [N.nameInfo n]
  ]

data NameInfo =
  NameInfo
  { name     :: String
  , typeSig  :: String
  , schema   :: Schema
  , modl     :: String
  , fixity   :: Maybe (String, Int)
  , pragmas  :: [String]
  , nameDocs :: Maybe String
  }

instance JSON.ToJSON NameInfo where
  toJSON (NameInfo{..}) =
    JSON.object $
    [ "name" .= name
    , "type string" .= typeSig
    , "type" .= JSONSchema schema
    , "module" .= modl
    ] ++
    maybe [] (\(assoc, lvl) ->
              [ "infix" .= True
              , "infix associativity" .= assoc
              , "infix level" .= lvl ]) fixity ++
    (if null pragmas then [] else ["pragmas" .= pragmas]) ++
    maybe [] (\d -> ["documentation" .= d]) nameDocs

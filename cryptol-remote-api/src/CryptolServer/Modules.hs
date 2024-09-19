{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.Modules
  ( visibleModules
  , visibleModulesDescr
  ) where

import qualified Argo.Doc as Doc
import qualified Data.Aeson as JSON
import Data.Aeson ((.=))
import qualified Data.Map as Map
import Data.Text (unpack)

import Cryptol.ModuleSystem.Env (loadedModules)
import Cryptol.ModuleSystem.Interface (ifsDoc)
import Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP (pp)

import CryptolServer (CryptolCommand, getModuleEnv)

data VisibleModulesParams = VisibleNamesParams

instance JSON.FromJSON VisibleModulesParams where
  parseJSON _ = pure VisibleNamesParams

instance Doc.DescribedMethod VisibleModulesParams [ModuleInfo] where
  parameterFieldDescription = []

  resultFieldDescription =
    [ ("name",
      Doc.Paragraph [Doc.Text "A human-readable representation of the name"])
    , ("documentation",
      Doc.Paragraph [Doc.Text "An optional field containing documentation string for the name, if it is documented"])
    ]

visibleModulesDescr :: Doc.Block
visibleModulesDescr =
  Doc.Paragraph [Doc.Text "List the currently visible (i.e., in scope) module names."]

visibleModules :: VisibleModulesParams -> CryptolCommand [ModuleInfo]
visibleModules _ = concatMap moduleToInfos . loadedModules <$> getModuleEnv


moduleToInfos :: T.Module -> [ModuleInfo]
moduleToInfos m =
  ModuleInfo
  { name = show (pp (T.mName m))
  , docs = map unpack (T.mDoc m)
  } :
  [ ModuleInfo
    { name = show (pp k)
    , docs = map unpack (ifsDoc (T.smIface v))
    }
    | (k,v) <- Map.assocs (T.mSubmodules m)
  ]

data ModuleInfo =
  ModuleInfo
  { name :: String
  , docs :: [String]
  }

instance JSON.ToJSON ModuleInfo where
  toJSON ModuleInfo{..} = JSON.object (("name" .= name) : ["documentation" .= docs | not (null docs)])

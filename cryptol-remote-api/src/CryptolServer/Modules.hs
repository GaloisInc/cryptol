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
import Cryptol.Utils.PP (PP, pp)

import CryptolServer (CryptolCommand, getModuleEnv)


data VisibleModulesParams = VisibleNamesParams

instance JSON.FromJSON VisibleModulesParams where
  parseJSON _ = pure VisibleNamesParams

instance Doc.DescribedMethod VisibleModulesParams [VisibleModuleInfo] where
  parameterFieldDescription = []

  resultFieldDescription =
    [ ("module",
      Doc.Paragraph [ Doc.Text "A human-readable representation of the module's name"])
    , ("documentation",
      Doc.Paragraph [ Doc.Text "An optional field containing documentation strings for the module,"
                    , Doc.Text "if it is documented"])
    , ("parameterized",
      Doc.Paragraph [ Doc.Text "A Boolean value indicating whether the focused module is"
                    , Doc.Text "parameterized"
                    ])
    ]

visibleModulesDescr :: Doc.Block
visibleModulesDescr =
  Doc.Paragraph [Doc.Text "List the currently visible (i.e., in scope) module names."]

visibleModules :: VisibleModulesParams -> CryptolCommand [VisibleModuleInfo]
visibleModules _ = concatMap (moduleToInfos False) . loadedModules <$> getModuleEnv


moduleToInfos :: PP a => Bool -> T.ModuleG a -> [VisibleModuleInfo]
moduleToInfos p m =
  ModuleInfo
  { name = show (pp (T.mName m))
  , parameterized = p
  , docs = map unpack (T.mDoc m)
  } :
  [ ModuleInfo
    { name = show (pp k)
    , parameterized = p
    , docs = map unpack (ifsDoc (T.smIface v))
    }
    | (k,v) <- Map.assocs (T.mSubmodules m)
  ] ++
  [ x
    | v <- Map.elems (T.mFunctors m)
    , x <- moduleToInfos True v
  ]

data VisibleModuleInfo =
  ModuleInfo
  { name :: String
  , parameterized :: Bool
  , docs :: [String]
  }

instance JSON.ToJSON VisibleModuleInfo where
  toJSON ModuleInfo{..} = JSON.object (
    [ "module" .= name
    , "parameterized" .= parameterized] ++
    ["documentation" .= docs | not (null docs)])

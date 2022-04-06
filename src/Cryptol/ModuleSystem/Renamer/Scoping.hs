{-# Language BlockArguments #-}
module Cryptol.ModuleSystem.Renamer.Scoping (scopingRelation) where

import Data.Map(Map)
import qualified Data.Map as Map

import Cryptol.Utils.Panic (panic)
import Cryptol.Parser.AST (ImpName,ImportG,iModule)
import Cryptol.ModuleSystem.Name (Name)
import Cryptol.ModuleSystem.NamingEnv (NamingEnv,interpImportEnv,shadowing)
import Cryptol.ModuleSystem.Binds (Mod(..))
import Cryptol.ModuleSystem.Renamer.Imports (ResolvedLocal,ResolvedModule(..))


{-| Compute the scoping relation for a module. -}
scopingRelation ::
  (ImpName Name -> Mod ())           {- ^ Info about external modules -} ->
  (Map (ImpName Name) ResolvedLocal) {- ^ Info about local modules -} ->
  NamingEnv                          {- ^ Things in the outer scope -} ->
  ImpName Name                       {- ^ Want scoping for this module -} ->
  NamingEnv
scopingRelation extMods locMods outer nm =
  case Map.lookup nm locMods of
    Just r ->
      let imps = mconcat [ doImport extMods locMods i | i <- rmodImports r ]
      in rmodDefines r `shadowing` imps `shadowing` outer

    Nothing ->
      panic "scopingRelation" ["Missing module", show nm]

doImport ::
  (ImpName Name -> Mod ()) ->
  (Map (ImpName Name) ResolvedLocal) ->
  ImportG (ImpName Name) ->
  NamingEnv
doImport extMods locMods imp =
  interpImportEnv imp
  case Map.lookup mname locMods of
    Nothing -> let m = extMods mname
               in if modParams m then mempty else modDefines (extMods mname)
    Just r  -> if rmodParams r then mempty else rmodDefines r
  where
  mname = iModule imp

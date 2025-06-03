module Load where

import Data.Map qualified as Map

import Cryptol.ModuleSystem
import Cryptol.ModuleSystem.Env(getLoadedEntities)
import qualified Language.LSP.Protocol.Types as LSP

import State
import Monad
import Index

doLoad :: LSP.Uri -> M ()
doLoad doc =
  case LSP.uriToFilePath doc of
    Just file ->
      doModuleCmd (loadModuleByPath file) \case
        Nothing -> pure ()
        Just _  ->
          update_ \s ->
            let env  = minpModuleEnv (cryState s)
                ents = Map.elems (getLoadedEntities (meLoadedModules env))
            in s { cryIndex = updateIndexes ents (cryIndex s) }
        
    Nothing -> pure ()
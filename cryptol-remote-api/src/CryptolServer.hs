{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer (module CryptolServer) where

import Control.Lens
import Control.Monad.IO.Class

import Cryptol.Eval.Monad (EvalOpts(..), PPOpts(..), PPFloatFormat(..), PPFloatExp(..))
import Cryptol.ModuleSystem (ModuleCmd, ModuleEnv)
import Cryptol.ModuleSystem.Env
  (getLoadedModules, lmFilePath, lmFingerprint, meLoadedModules,
   initialModuleEnv, meSearchPath, ModulePath(..))
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.Parser.AST (ModName)
import Cryptol.Utils.Logger (quietLogger)

import Argo
import CryptolServer.Exceptions

runModuleCmd :: ModuleCmd a -> Method ServerState a
runModuleCmd cmd =
    do s <- getState
       reader <- getFileReader
       out <- liftIO $ cmd (theEvalOpts, reader, view moduleEnv s)
       case out of
         (Left x, warns) ->
           raise (cryptolError x warns)
         (Right (x, newEnv), _warns) ->
           -- TODO: What to do about warnings when a command completes
           -- successfully?
           do setState (set moduleEnv newEnv s)
              return x

data LoadedModule = LoadedModule
  { _loadedName :: Maybe ModName   -- ^ Working on this module.
  , _loadedPath :: FilePath        -- ^ Working on this file.
  }

loadedName :: Lens' LoadedModule (Maybe ModName)
loadedName = lens _loadedName (\v n -> v { _loadedName = n })

loadedPath :: Lens' LoadedModule FilePath
loadedPath = lens _loadedPath (\v n -> v { _loadedPath = n })


data ServerState =
  ServerState { _loadedModule :: Maybe LoadedModule
              , _moduleEnv :: ModuleEnv
              }

loadedModule :: Lens' ServerState (Maybe LoadedModule)
loadedModule = lens _loadedModule (\v n -> v { _loadedModule = n })

moduleEnv :: Lens' ServerState ModuleEnv
moduleEnv = lens _moduleEnv (\v n -> v { _moduleEnv = n })

initialState :: IO ServerState
initialState = ServerState Nothing <$> initialModuleEnv

setSearchPath :: [FilePath] -> ServerState -> ServerState
setSearchPath paths =
  over moduleEnv $ \me -> me { meSearchPath = paths ++ meSearchPath me }

theEvalOpts :: EvalOpts
theEvalOpts = EvalOpts quietLogger (PPOpts False 10 25 10 (FloatFree AutoExponent))

-- | Check that all of the modules loaded in the Cryptol environment
-- currently have fingerprints that match those when they were loaded.
validateServerState :: ServerState -> IO Bool
validateServerState =
  foldr check (return True) . getLoadedModules . meLoadedModules . view moduleEnv
  where
    check lm continue =
      case lmFilePath lm of
        InMem{} -> continue
        InFile file ->
          do fp <- fingerprintFile file
             if fp == Just (lmFingerprint lm)
               then continue
               else return False

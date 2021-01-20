{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module CryptolServer (module CryptolServer) where

import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT(ReaderT))
import qualified Data.Aeson as JSON
import Data.Text (Text)

import Cryptol.Eval (EvalOpts(..))
import Cryptol.ModuleSystem (ModuleCmd, ModuleEnv, ModuleInput(..))
import Cryptol.ModuleSystem.Env
  (getLoadedModules, lmFilePath, lmFingerprint, meLoadedModules,
   initialModuleEnv, meSearchPath, ModulePath(..))
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.Parser.AST (ModName)

import qualified Argo
import qualified Argo.Doc as Doc
import CryptolServer.Exceptions
import CryptolServer.Options

newtype CryptolMethod a = CryptolMethod { runCryptolMethod :: Options -> Argo.Method ServerState a }
  deriving (Functor, Applicative, Monad, MonadIO) via ReaderT Options (Argo.Method ServerState)

method ::
  forall params result.
  (JSON.FromJSON params, JSON.ToJSON result, Doc.DescribedParams params) =>
  Text ->
  Argo.MethodType ->
  Doc.Block ->
  (params -> CryptolMethod result) ->
  Argo.AppMethod ServerState
method name ty doc f = Argo.method name ty doc f'
  where f' (WithOptions opts params) = runCryptolMethod (f params) opts


getOptions :: CryptolMethod Options
getOptions = CryptolMethod pure

getEvalOpts :: CryptolMethod EvalOpts
getEvalOpts = optEvalOpts <$> getOptions

raise :: Argo.JSONRPCException -> CryptolMethod a
raise = CryptolMethod . const . Argo.raise

getModuleEnv :: CryptolMethod ModuleEnv
getModuleEnv =
  CryptolMethod $ const $ view moduleEnv <$> Argo.getState

setModuleEnv :: ModuleEnv -> CryptolMethod ()
setModuleEnv me =
  CryptolMethod $ const $ Argo.getState >>= \s -> Argo.setState (set moduleEnv me s)

runModuleCmd :: ModuleCmd a -> CryptolMethod a
runModuleCmd cmd =
    do Options callStacks evOpts <- getOptions
       s <- CryptolMethod $ const Argo.getState
       reader <- CryptolMethod $ const Argo.getFileReader
       let minp = ModuleInput
                  { minpCallStacks = callStacks
                  , minpEvalOpts   = pure evOpts
                  , minpByteReader = reader
                  , minpModuleEnv  = view moduleEnv s
                  }
       out <- liftIO $ cmd minp
       case out of
         (Left x, warns) ->
           raise (cryptolError x warns)
         (Right (x, newEnv), _warns) ->
           -- TODO: What to do about warnings when a command completes
           -- successfully?
           do setModuleEnv newEnv
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

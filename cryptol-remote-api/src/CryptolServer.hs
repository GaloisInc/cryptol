{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module CryptolServer (module CryptolServer) where

import Control.Lens
import Control.Concurrent.MVar
import qualified Control.Exception as X
import Control.Monad (unless)
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT(ReaderT))
import qualified Data.Aeson as JSON
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Set as Set
import Data.Text (Text)

import Cryptol.Eval (EvalOpts(..))
import Cryptol.IR.FreeVars (FreeVars)
import Cryptol.ModuleSystem
  (ModuleCmd, ModuleEnv(..), ModuleInput(..))
import Cryptol.ModuleSystem.Env
  (getLoadedModules, loadedParamModDeps, lmFilePath, lmFileInfo, fiFingerprint,
   initialModuleEnv, ModulePath(..))
import Cryptol.ModuleSystem.Name (FreshM(..))
import Cryptol.ModuleSystem.Fingerprint ( fingerprintFile )
import Cryptol.Parser.AST (ModName)
import Cryptol.TypeCheck( defaultSolverConfig )
import qualified Cryptol.TypeCheck.Solver.SMT as SMT

import qualified Argo
import qualified Argo.Doc as Doc
import CryptolServer.Exceptions
  ( cryptolError, evalInParamMod, tcSolverTimeout )
import CryptolServer.Options
    ( WithOptions(WithOptions), Options(Options, optEvalOpts) )

newtype CryptolCommand a = CryptolCommand { runCryptolCommand :: Options -> Argo.Command ServerState a }
  deriving (Functor, Applicative, Monad, MonadIO) via ReaderT Options (Argo.Command ServerState)

newtype CryptolNotification a = CryptolNotification { runCryptolNotification :: Options -> Argo.Notification a }
  deriving (Functor, Applicative, Monad, MonadIO) via ReaderT Options Argo.Notification

command ::
  forall params result.
  (JSON.FromJSON params, JSON.ToJSON result, Doc.DescribedMethod params result) =>
  Text ->
  Doc.Block ->
  (params -> CryptolCommand result) ->
  Argo.AppMethod ServerState
command name doc f = Argo.command name doc f'
  where f' (WithOptions opts params) = runCryptolCommand (f params) opts


notification ::
  forall params.
  (JSON.FromJSON params, Doc.DescribedMethod params ()) =>
  Text ->
  Doc.Block ->
  (params -> CryptolNotification ()) ->
  Argo.AppMethod ServerState
notification name doc f = Argo.notification name doc f'
  where f' (WithOptions opts params) = runCryptolNotification (f params) opts

class CryptolMethod m where
  getOptions :: m Options
  getEvalOpts :: m EvalOpts
  raise :: Argo.JSONRPCException -> m a

instance CryptolMethod CryptolCommand where
  getOptions = CryptolCommand pure
  getEvalOpts = optEvalOpts <$> getOptions
  raise = CryptolCommand . const . Argo.raise

instance CryptolMethod CryptolNotification where
  getOptions = CryptolNotification pure
  getEvalOpts = optEvalOpts <$> getOptions
  raise = CryptolNotification . const . Argo.raise

getModuleEnv :: CryptolCommand ModuleEnv
getModuleEnv = CryptolCommand $ const $ view moduleEnv <$> Argo.getState

setModuleEnv :: ModuleEnv -> CryptolCommand ()
setModuleEnv me =
  CryptolCommand $ const $ Argo.getState >>= \s -> Argo.setState (set moduleEnv me s)

modifyModuleEnv :: (ModuleEnv -> ModuleEnv) -> CryptolCommand ()
modifyModuleEnv f =
  CryptolCommand $ const $ Argo.getState >>= \s -> Argo.setState (set moduleEnv (f (view moduleEnv s)) s)

getTCSolverRef :: CryptolCommand (MVar (Maybe SMT.Solver))
getTCSolverRef =
  CryptolCommand $ const $ view tcSolver <$> Argo.getState

getTCSolverConfig :: CryptolCommand SMT.SolverConfig
getTCSolverConfig = CryptolCommand $ const $ solverConfig <$> Argo.getState

getTCSolver :: CryptolCommand SMT.Solver
getTCSolver =
  do ref <- getTCSolverRef
     cfg <- getTCSolverConfig
     liftIO (getTCSolverIO ref cfg)

getTCSolverForState :: ServerState -> IO SMT.Solver
getTCSolverForState s =
  getTCSolverIO (view tcSolver s) (solverConfig s)

getTCSolverIO ::
  MVar (Maybe SMT.Solver) -> SMT.SolverConfig -> IO SMT.Solver
getTCSolverIO ref cfg =
  modifyMVar ref $ \mb ->
    case mb of
      Just solver ->
        pure (mb, solver)
      Nothing ->
        do let onExit = modifyMVar_ ref (const (pure Nothing))
           solver <- SMT.startSolver onExit cfg
           pure (Just solver, solver)

catchTCSolverTimeout :: IO a -> CryptolCommand a
catchTCSolverTimeout action =
  do result <- liftIO (X.try action)
     case result of
       Right a ->
         pure a
       Left (SMT.SolverTimeout seconds) ->
         raise (tcSolverTimeout seconds)

runTCSolver :: (SMT.Solver -> IO a) -> CryptolCommand a
runTCSolver action =
  do s <- getTCSolver
     catchTCSolverTimeout (action s)

liftModuleCmd :: ModuleCmd a -> CryptolCommand a
liftModuleCmd cmd =
    do Options callStacks evOpts <- getOptions
       s <- CryptolCommand $ const Argo.getState
       reader <- CryptolCommand $ const Argo.getFileReader
       solver <- getTCSolver
       let minp = ModuleInput
                  { minpCallStacks = callStacks
                  , minpSaveRenamed = False
                  , minpEvalOpts   = pure evOpts
                  , minpByteReader = reader
                  , minpModuleEnv  = view moduleEnv s
                  , minpTCSolver   = solver
                  }
       out <- liftIO (cmd minp)
       case out of
         (Left x, warns) ->
           raise (cryptolError x warns)
         (Right (x, newEnv), _warns) ->
           -- TODO: What to do about warnings when a command completes
           -- successfully?
           do setModuleEnv newEnv
              return x

-- | Is evaluation enabled? If the currently focused module is parameterized,
-- then we cannot evaluate.
--
-- See also the 'validEvalContext' function in @Cryptol.REPL.Monad@, on which
-- this function is based.
validEvalContext :: FreeVars a => a -> CryptolCommand ()
validEvalContext a =
  do me <- getModuleEnv
     let (badTs, bad) = loadedParamModDeps (meLoadedModules me) a
     unless (Set.null bad && Set.null badTs) $
       raise (evalInParamMod (Set.toList badTs) (Set.toList bad))

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
              , _tcSolver :: MVar (Maybe SMT.Solver)
              , solverConfig :: SMT.SolverConfig
              }

loadedModule :: Lens' ServerState (Maybe LoadedModule)
loadedModule = lens _loadedModule (\v n -> v { _loadedModule = n })

moduleEnv :: Lens' ServerState ModuleEnv
moduleEnv = lens _moduleEnv (\v n -> v { _moduleEnv = n })

tcSolver :: Lens' ServerState (MVar (Maybe SMT.Solver))
tcSolver = lens _tcSolver (\v n -> v { _tcSolver = n })


initialState :: IO ServerState
initialState =
  do modEnv <- initialModuleEnv
     let sCfg = defaultSolverConfig (meSearchPath modEnv)
     solverRef <- newMVar Nothing
     pure (ServerState Nothing modEnv solverRef sCfg)

extendSearchPath :: [FilePath] -> ServerState -> ServerState
extendSearchPath paths =
  over moduleEnv $ \me -> me { meSearchPath = nubOrd $ paths ++ meSearchPath me }


resetTCSolver :: CryptolCommand ()
resetTCSolver = do
  ref <- getTCSolverRef
  solver <- liftIO $
    modifyMVar ref $ \mb ->
      pure (Nothing, mb)
  case solver of
    Nothing -> pure ()
    Just s  -> liftIO (SMT.stopSolver s)

instance FreshM CryptolCommand where
  liftSupply f = do
    serverState <- CryptolCommand $ const Argo.getState
    let mEnv = view moduleEnv serverState
        (res, supply') = f (meSupply $ mEnv)
        mEnv' = mEnv { meSupply = supply' }
    CryptolCommand $ const (Argo.modifyState $ set moduleEnv mEnv')
    pure res

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
             if fp == Right (fiFingerprint (lmFileInfo lm))
               then continue
               else return False

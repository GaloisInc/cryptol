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
import Data.Containers.ListUtils (nubOrd)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Text (Text)

import Cryptol.Eval (EvalOpts(..))
import Cryptol.ModuleSystem (ModuleCmd, ModuleEnv(..), ModuleInput(..))
import Cryptol.ModuleSystem.Env
  (getLoadedModules, lmFilePath, lmFingerprint,
   initialModuleEnv, ModulePath(..))
import Cryptol.ModuleSystem.Name (Name, FreshM(..), nameUnique, nameIdent)
import Cryptol.ModuleSystem.Fingerprint ( fingerprintFile )
import Cryptol.Parser.AST (ModName, isInfixIdent)
import Cryptol.TypeCheck( defaultSolverConfig )
import qualified Cryptol.TypeCheck.Solver.SMT as SMT

import qualified Argo
import qualified Argo.Doc as Doc
import CryptolServer.Data.FreshName
import CryptolServer.Exceptions
    ( cryptolError, invalidName)
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

getTCSolver :: CryptolCommand SMT.Solver
getTCSolver = CryptolCommand $ const $ view tcSolver <$> Argo.getState

liftModuleCmd :: ModuleCmd a -> CryptolCommand a
liftModuleCmd cmd =
    do Options callStacks evOpts <- getOptions
       s <- CryptolCommand $ const Argo.getState
       reader <- CryptolCommand $ const Argo.getFileReader
       let minp = ModuleInput
                  { minpCallStacks = callStacks
                  , minpEvalOpts   = pure evOpts
                  , minpByteReader = reader
                  , minpModuleEnv  = view moduleEnv s
                  , minpTCSolver   = view tcSolver s
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
              , _tcSolver :: SMT.Solver
              , _freshNameEnv :: IntMap Name
              }

loadedModule :: Lens' ServerState (Maybe LoadedModule)
loadedModule = lens _loadedModule (\v n -> v { _loadedModule = n })

moduleEnv :: Lens' ServerState ModuleEnv
moduleEnv = lens _moduleEnv (\v n -> v { _moduleEnv = n })

tcSolver :: Lens' ServerState SMT.Solver
tcSolver = lens _tcSolver (\v n -> v { _tcSolver = n })

-- | Names generated when marshalling complex values to an RPC client;
-- maps `nameUnique`s to `Name`s.
freshNameEnv :: Lens' ServerState (IntMap Name)
freshNameEnv = lens _freshNameEnv (\v n -> v { _freshNameEnv = n })


-- | Take and remember the given name so it can later be recalled
-- via it's `nameUnique` unique identifier. Return a `FreshName`
-- which can be easily serialized/pretty-printed and marshalled
-- across an RPC interface.
registerName :: Name -> CryptolCommand FreshName
registerName nm =
  if isInfixIdent (nameIdent nm)
  then raise $ invalidName nm
  else
    CryptolCommand $ const $ Argo.getState >>= \s ->
      let nmEnv = IntMap.insert (nameUnique nm) nm (view freshNameEnv s)
      in do Argo.setState (set freshNameEnv nmEnv s)
            pure $ unsafeToFreshName nm

-- | Return the underlying `Name` the given `FreshName` refers to. The
-- `FreshName` should have previously been returned by `registerName` at some
-- point, or else a JSON exception will be raised.
resolveFreshName :: FreshName -> CryptolCommand (Maybe Name)
resolveFreshName fnm =
  CryptolCommand $ const $ Argo.getState >>= \s ->
    case IntMap.lookup (freshNameUnique fnm) (view freshNameEnv s) of
      Nothing -> pure Nothing
      Just nm -> pure $ Just nm


initialState :: IO ServerState
initialState =
  do modEnv <- initialModuleEnv
     s <- SMT.startSolver (defaultSolverConfig (meSearchPath modEnv))
     pure (ServerState Nothing modEnv s IntMap.empty)

extendSearchPath :: [FilePath] -> ServerState -> ServerState
extendSearchPath paths =
  over moduleEnv $ \me -> me { meSearchPath = nubOrd $ paths ++ meSearchPath me }


instance FreshM CryptolCommand where
  liftSupply f = do
    serverState <- CryptolCommand $ const Argo.getState
    let mEnv = view moduleEnv serverState
        (res, supply') = f (meSupply $ mEnv)
        mEnv' = mEnv { meSupply = supply' }
    CryptolCommand $ const (Argo.modifyState $ set moduleEnv mEnv')
    pure res

freshNameCount :: CryptolCommand Int
freshNameCount = CryptolCommand $ const $ do
  fEnv <- view freshNameEnv <$> Argo.getState
  pure $ IntMap.size fEnv


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

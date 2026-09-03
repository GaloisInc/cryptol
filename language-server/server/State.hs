module State where

import Data.ByteString qualified as BS
import Data.Text(Text)
import Data.Text qualified as Text
import Data.Map(Map)
import Control.Exception
import Control.Concurrent
import Control.Concurrent.STM.TVar
import Data.Aeson qualified as JS
import Data.Aeson.Types qualified as JS
import Language.LSP.Protocol.Types qualified as LSP

import Cryptol.Utils.Logger(funLogger)
import Cryptol.ModuleSystem
import Cryptol.TypeCheck.Solver.SMT (Solver, startSolver, killSolver)
import Cryptol.TypeCheck.InferTypes(defaultSolverConfig)
import Cryptol.Eval.Value(EvalOpts(..), defaultPPOpts)

import Index

-- | Configuration and state of the server
data Config = Config {
  stateRef   :: MVar State,
  -- ^ This control access to the state.  Generally we should not
  -- hold this for a long time as it blocks the server.

  cryWorking :: MVar (),
  -- ^ We take this when doing something the might update the
  -- Cryptol state (`cryEnv`, e.g., loading modules).
  -- We do this instead of taking the `stateRef` so that the server can still
  -- read the state while we are working on computing the new Cryptol state.

  cryLog :: MVar (Text -> IO ()),
  -- ^ A callback to use to send messages to the client

  cryTCSolver :: MVar (Maybe Solver),
  -- ^ Holds the current typechecker solver, if one is running.  When `Nothing`,
  -- the next module command starts a fresh solver and saves it here.

  crySearchPath :: [FilePath]
  -- ^ Search path for modules
}

data State = State {
  lexedFiles      :: Map LSP.NormalizedUri ([LSP.SemanticTokenAbsolute], [LSP.FoldingRange]),
  -- ^ Cache of lexed files

  cryRoots        :: Map LSP.NormalizedUri (ThreadId, TVar Bool),
  -- ^ Open files.  For each files we have a thread monitoring the file,
  -- which re-lexes it on change.  The `TVar` is to signal that a file
  -- has changed, used so that we can wait until the user has stopped
  -- typing for a bit.

  cryIndex        :: IndexDB,
  -- ^ Information we get from passes after lexer:
  -- additional sematnic token information, doc strings, types, etc.

  cryEnv          :: ModuleEnv
  -- ^ State of the Cryptol module environment
}


-- | Make a fresh server state with the default configuration.
newConfig :: IO Config
newConfig =
  do
    me     <- initialModuleEnv
    logCallback <- newEmptyMVar
    solverRef <- newMVar Nothing
    work   <- newMVar ()
    ref    <- newMVar State {
      lexedFiles = mempty,
      cryIndex = emptyIndexDB,
      cryRoots = mempty,
      cryEnv = me
    }
    pure Config
      { stateRef = ref
      , cryLog = logCallback
      , cryTCSolver = solverRef
      , cryWorking = work
      , crySearchPath = []
      }

-- | Kill the SMT solver for this configuration.
stopConfig :: Config -> IO ()
stopConfig cfg =
  (do solver <- modifyMVar (cryTCSolver cfg) \mb ->
                  pure (Nothing, mb)
      case solver of
        Nothing -> pure ()
        Just s  -> killSolver s)
  `catch` \SomeException {} -> pure ()

-- | Get the current typechecker solver, starting one if needed.
getTCSolver :: Config -> IO Solver
getTCSolver cfg =
  modifyMVar (cryTCSolver cfg) \mb ->
    case mb of
      Just solver ->
        pure (mb, solver)
      Nothing ->
        do
          let onExit = modifyMVar_ (cryTCSolver cfg) (const (pure Nothing))
          solver <- startSolver onExit (defaultSolverConfig [])
          pure (Just solver, solver)

-- | Construct the input for a module command, starting the typechecker solver
-- if the previous solver exited.
getModuleInput :: Config -> State -> IO (ModuleInput IO)
getModuleInput cfg s =
  do solver <- getTCSolver cfg
     pure ModuleInput
       { minpCallStacks = True
       , minpEvalOpts =
           pure EvalOpts
             { evalLogger = funLogger \str ->
                 do mb <- tryReadMVar (cryLog cfg)
                    case mb of
                      Nothing  -> pure ()
                      Just msg -> msg (Text.pack str)
             , evalPPOpts = defaultPPOpts
             }
       , minpByteReader = BS.readFile
       , minpModuleEnv = cryEnv s
       , minpTCSolver = solver
       , minpSaveRenamed = True
       }


-- | Update the settings based on some JSON that came from the client.
parseConfig :: Config -> JS.Value -> Either Text Config
parseConfig old = either (Left . Text.pack) Right . JS.parseEither parser
  where
  parser =
    JS.withObject "Configuration" \obj ->
      do
        path <- obj JS..: "search-path"
        pure old { crySearchPath = path }

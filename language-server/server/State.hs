module State where

import Data.ByteString qualified as BS
import Data.Text(Text)
import Data.Text qualified as Text
import Data.Set(Set)
import Data.Map(Map)
import Control.Exception
import Control.Concurrent
import Data.Aeson qualified as JS
import Data.Aeson.Types qualified as JS
import Language.LSP.Protocol.Types qualified as LSP

import Cryptol.Utils.Logger(funLogger)
import Cryptol.ModuleSystem
import Cryptol.TypeCheck.Solver.SMT (startSolver, killSolver)
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
  -- Cryptol state (`cryState`, e.g., loading modules).
  -- We do this instead of taking the `stateRef` so that the server can still
  -- read the state while we are working on computing the new Cryptol state.

  cryLog :: MVar (Text -> IO ()),
  -- ^ A callback to use to send messages to the client

  crySearchPath :: [FilePath]
  -- ^ Search path for modules
}

data State = State {
  lexedFiles  :: Map LSP.NormalizedUri ([LSP.SemanticTokenAbsolute], [LSP.FoldingRange]),
  cryRoots    :: Set LSP.NormalizedUri,
  cryIndex    :: IndexDB,
  cryState    :: ModuleInput IO
}


-- | Make a fresh server state with the default configuration.
newConfig :: IO Config
newConfig =
  do
    solver <- startSolver (pure ()) (defaultSolverConfig [])
    me     <- initialModuleEnv
    logCallback <- newEmptyMVar
    work   <- newMVar ()
    ref    <- newMVar State {
      lexedFiles = mempty,
      cryIndex = emptyIndexDB,
      cryRoots = mempty,
      cryState = ModuleInput {
        minpCallStacks = True,
        minpEvalOpts =
          pure EvalOpts {
          evalLogger  = funLogger \str ->
            do
              mb <- tryReadMVar logCallback
              case mb of
                Nothing  -> pure ()
                Just msg -> msg (Text.pack str),
          evalPPOpts  = defaultPPOpts
        },
        minpByteReader  = BS.readFile,
        minpModuleEnv   = me,
        minpTCSolver    = solver,
        minpSaveRenamed = True
      }
    }
    pure Config { stateRef = ref, cryLog = logCallback, cryWorking = work, crySearchPath = [] } 

-- | Kill the SMT solver for this configuration.
stopConfig :: Config -> IO ()
stopConfig cfg = withMVar (stateRef cfg) (killSolver . minpTCSolver . cryState)
  `catch` \SomeException {} -> pure ()


-- | Update the settings based on some JSON that came from the client.
parseConfig :: Config -> JS.Value -> Either Text Config
parseConfig old = either (Left . Text.pack) Right . JS.parseEither parser
  where
  parser =
    JS.withObject "Configuration" \obj ->
      do
        path <- obj JS..: "search-path"
        pure old { crySearchPath = path }


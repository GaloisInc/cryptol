module State where

import Data.ByteString qualified as BS
import Data.Text(Text)
import Data.Map(Map)
import Control.Exception
import Control.Concurrent
import Data.Aeson qualified as JS
import Language.LSP.Protocol.Types qualified as LSP

import Cryptol.Utils.Logger(quietLogger)
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

  cryWorking :: MVar ()
  -- ^ We take this when doing something the might update the
  -- Cryptol state (`cryState`, e.g., loading modules).
  -- We do this instead of taking the `stateRef` so that the server can still
  -- read the state while we are working on computing the new Cryptol state.
}

data State = State {
  lexedFiles  :: Map LSP.Uri ([LSP.SemanticTokenAbsolute], [LSP.FoldingRange]),
  cryIndex    :: IndexDB,
  cryState    :: ModuleInput IO
}

-- | Make a fresh server state with the default configuration.
newConfig :: IO Config
newConfig =
  do
    solver <- startSolver (pure ()) (defaultSolverConfig [])
    me     <- initialModuleEnv
    work   <- newMVar ()
    ref    <- newMVar State {
      lexedFiles = mempty,
      cryIndex = emptyIndexDB,
      cryState = ModuleInput {
        minpCallStacks = True,
        minpEvalOpts = pure EvalOpts {
          evalLogger  = quietLogger,
          evalPPOpts  = defaultPPOpts
        },
        minpByteReader  = BS.readFile,
        minpModuleEnv   = me,
        minpTCSolver    = solver,
        minpSaveRenamed = True
      }
    }
    pure Config { stateRef = ref, cryWorking = work } 

-- | Kill the SMT solver for this configuration.
stopConfig :: Config -> IO ()
stopConfig cfg = withMVar (stateRef cfg) (killSolver . minpTCSolver . cryState)
  `catch` \SomeException {} -> pure ()


-- | Update the settings based on some JSON that came from the client.
parseConfig :: Config -> JS.Value -> Either Text Config
parseConfig old _upd = Right old

module GitRev.TH where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.Maybe
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import System.Directory
import System.FilePath
import System.Process

-- | Run git with the given arguments and no stdin, returning the
-- stdout output. If git isn't available or something goes wrong,
-- return the second argument.
runGit :: [String] -> String -> Q String
runGit args def = do
  let oops :: SomeException -> IO String
      oops _e = return def
  gitFound <- runIO $ isJust <$> findExecutable "git"
  if gitFound
    then do
      -- a lot of bookkeeping to record the right dependencies
      pwd <- runIO $ getCurrentDirectory
      let hd         = pwd </> ".git" </> "HEAD"
          index      = pwd </> ".git" </> "index"
          packedRefs = pwd </> ".git" </> "packed-refs"
      hdExists  <- runIO $ doesFileExist hd
      when hdExists $ do
        -- the HEAD file either contains the hash of a detached head
        -- or a pointer to the file that contains the hash of the head
        hdRef <- runIO $ readFile hd
        case splitAt 5 hdRef of
          -- pointer to ref
          ("ref: ", relRef) -> do
            let ref = pwd </> ".git" </> relRef
            refExists <- runIO $ doesFileExist ref
            when refExists $ addDependentFile ref
          -- detached head
          _hash -> addDependentFile hd
      -- add the index if it exists to set the dirty flag
      indexExists <- runIO $ doesFileExist index
      when indexExists $ addDependentFile index
      -- if the refs have been packed, the info we're looking for
      -- might be in that file rather than the one-file-per-ref case
      -- handled above
      packedExists <- runIO $ doesFileExist packedRefs
      when packedExists $ addDependentFile packedRefs
      runIO $ (takeWhile (/= '\n') <$> readProcess "git" args "") `catch` oops
    else return def

getHash :: ExpQ
getHash =
  stringE =<< runGit ["rev-parse", "HEAD"] "UNKNOWN"

getBranch :: ExpQ
getBranch =
  stringE =<< runGit ["rev-parse", "--abbrev-ref", "HEAD"] "UNKNOWN"

getDirty :: ExpQ
getDirty = do
  output <- runGit ["status", "--porcelain"] ""
  case output of
    "" -> conE $ mkName "Prelude.False"
    _  -> conE $ mkName "Prelude.True"

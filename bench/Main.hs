-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
module Main where

import Control.DeepSeq

import qualified Data.Text.Lazy     as T
import qualified Data.Text.Lazy.IO  as T

import qualified Cryptol.ModuleSystem.Base  as M
import qualified Cryptol.ModuleSystem.Env   as M
import qualified Cryptol.ModuleSystem.Monad as M

import qualified Cryptol.Parser           as P
import qualified Cryptol.Parser.AST       as P
import qualified Cryptol.Parser.NoInclude as P

import qualified Cryptol.TypeCheck as T

import Criterion.Main

main :: IO ()
main = defaultMain [
    bgroup "parser" [
        parser "Prelude" "lib/Cryptol.cry"
      , parser "BigSequence" "bench/data/BigSequence.cry"
      ]
  , bgroup "typechecker" [
        tc "Prelude" "lib/Cryptol.cry"
      , tc "BigSequence" "bench/data/BigSequence.cry"
      ]
  ]

-- | Make a benchmark for parsing a Cryptol module
parser :: String -> FilePath -> Benchmark
parser name path =
  env (T.readFile path) $ \(~bytes) ->
    bench name $ whnfIO $ do
      let cfg = P.defaultConfig
                { P.cfgSource  = path
                , P.cfgPreProc = P.guessPreProc path
                }
      case P.parseModule cfg bytes of
        Right pm -> return pm
        Left err -> error (show err)

-- | Make a benchmark for typechecking a Cryptol module. Does parsing
-- in the setup phase in order to isolate typechecking
tc :: String -> FilePath -> Benchmark
tc name path =
  let setup = do
        bytes <- T.readFile path
        let cfg = P.defaultConfig
                { P.cfgSource  = path
                , P.cfgPreProc = P.guessPreProc path
                }
            Right pm = P.parseModule cfg bytes
        menv <- M.initialModuleEnv
        (Right (scm, menv'), _) <- M.runModuleM menv $ do
          -- code from `loadModule` and `checkModule` in
          -- `Cryptol.ModuleSystem.Base`
          let pm' = M.addPrelude pm
          M.loadDeps pm'
          Right nim <- M.io (P.removeIncludesModule path pm')
          npm <- M.noPat nim
          M.renameModule npm
        return (scm, menv')
  in env setup $ \ ~(scm, menv) ->
    bench name $ whnfIO $ M.runModuleM menv $ do
      let act = M.TCAction { M.tcAction = T.tcModule
                           , M.tcLinter = M.moduleLinter (P.thing (P.mName scm)) }
      M.typecheck act scm =<< M.importIfacesTc (map P.thing (P.mImports scm))

-- FIXME: this should only throw off the first benchmark run, but still...
instance NFData P.Module where
  rnf _ = ()

-- FIXME: this should only throw off the first benchmark run, but still...
instance NFData M.ModuleEnv where
  rnf _ = ()

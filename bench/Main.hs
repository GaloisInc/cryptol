-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Data.Text.Lazy     as T
import qualified Data.Text.Lazy.IO  as T

import qualified Cryptol.ModuleSystem.Base      as M
import qualified Cryptol.ModuleSystem.Env       as M
import qualified Cryptol.ModuleSystem.Monad     as M
import qualified Cryptol.ModuleSystem.NamingEnv as M

import qualified Cryptol.Parser           as P
import qualified Cryptol.Parser.AST       as P
import qualified Cryptol.Parser.NoInclude as P

import qualified Cryptol.Symbolic as S

import qualified Cryptol.TypeCheck     as T
import qualified Cryptol.TypeCheck.AST as T

import qualified Cryptol.Utils.Ident as I

import Criterion.Main

main :: IO ()
main = defaultMain [
    bgroup "parser" [
        parser "Prelude" "lib/Cryptol.cry"
      , parser "BigSequence" "bench/data/BigSequence.cry"
      , parser "BigSequenceHex" "bench/data/BigSequenceHex.cry"
      , parser "AES" "bench/data/AES.cry"
      , parser "SHA512" "bench/data/SHA512.cry"
      ]
  , bgroup "typechecker" [
        tc "Prelude" "lib/Cryptol.cry"
      , tc "BigSequence" "bench/data/BigSequence.cry"
      , tc "BigSequenceHex" "bench/data/BigSequenceHex.cry"
      , tc "AES" "bench/data/AES.cry"
      , tc "SHA512" "bench/data/SHA512.cry"
      ]
  , bgroup "conc_eval" [
        ceval "AES" "bench/data/AES.cry" "bench bench_data"
      , ceval "SHA512" "bench/data/SHA512.cry" "testVector1 ()"
      ]
  , bgroup "sym_eval" [
        seval "AES" "bench/data/AES.cry" "aesEncrypt (zero, zero)"
      , seval "ZUC" "bench/data/ZUC.cry"
          "ZUC_isResistantToCollisionAttack"
      , seval "SHA512" "bench/data/SHA512.cry" "testVector1 ()"
      ]
  ]

-- | Make a benchmark for parsing a Cryptol module
parser :: String -> FilePath -> Benchmark
parser name path =
  env (T.readFile path) $ \(~bytes) ->
    bench name $ nfIO $ do
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
        (Right ((prims, scm, tcEnv), menv'), _) <- M.runModuleM menv $ do
          -- code from `loadModule` and `checkModule` in
          -- `Cryptol.ModuleSystem.Base`
          let pm' = M.addPrelude pm
          M.loadDeps pm'
          Right nim <- M.io (P.removeIncludesModule path pm')
          npm <- M.noPat nim
          (tcEnv,declsEnv,scm) <- M.renameModule npm
          prims <- if P.thing (P.mName pm) == I.preludeName
                   then return (M.toPrimMap declsEnv)
                   else M.getPrimMap
          return (prims, scm, tcEnv)
        return (prims, scm, tcEnv, menv')
  in env setup $ \ ~(prims, scm, tcEnv, menv) ->
    bench name $ nfIO $ M.runModuleM menv $ do
      let act = M.TCAction { M.tcAction = T.tcModule
                           , M.tcLinter = M.moduleLinter (P.thing (P.mName scm))
                           , M.tcPrims  = prims
                           }
      M.typecheck act scm tcEnv

ceval :: String -> FilePath -> T.Text -> Benchmark
ceval name path expr =
  let setup = do
        menv <- M.initialModuleEnv
        (Right (texpr, menv'), _) <- M.runModuleM menv $ do
          m <- M.loadModuleByPath path
          M.setFocusedModule (T.mName m)
          let Right pexpr = P.parseExpr expr
          (_, texpr, _) <- M.checkExpr pexpr
          return texpr
        return (texpr, menv')
  in env setup $ \ ~(texpr, menv) ->
    bench name $ nfIO $ M.runModuleM menv $ M.evalExpr texpr

seval :: String -> FilePath -> T.Text -> Benchmark
seval name path expr =
  let setup = do
        menv <- M.initialModuleEnv
        (Right (texpr, menv'), _) <- M.runModuleM menv $ do
          m <- M.loadModuleByPath path
          M.setFocusedModule (T.mName m)
          let Right pexpr = P.parseExpr expr
          (_, texpr, _) <- M.checkExpr pexpr
          return texpr
        return (texpr, menv')
  in env setup $ \ ~(texpr, menv) ->
    bench name $ flip nf texpr $ \texpr' ->
      let senv = S.evalDecls mempty (S.allDeclGroups menv)
      in S.evalExpr senv texpr'

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.ModuleSystem (
    -- * Module System
    ModuleEnv(..), initialModuleEnv
  , ModuleError(..), ModuleWarning(..)
  , ModuleCmd, ModuleRes
  , findModule
  , loadModuleByPath
  , loadModule
  , checkExpr
  , evalExpr
  , focusedEnv

    -- * Interfaces
  , Iface(..), IfaceDecls(..), genIface
  , IfaceTySyn, IfaceDecl(..)
  ) where

import qualified Cryptol.Eval.Value        as E
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Interface
import           Cryptol.ModuleSystem.Monad
import qualified Cryptol.ModuleSystem.Base as Base
import qualified Cryptol.Parser.AST        as P
import qualified Cryptol.TypeCheck.AST     as T


-- Public Interface ------------------------------------------------------------

type ModuleCmd a = ModuleEnv -> IO (ModuleRes a)

type ModuleRes a = (Either ModuleError (a,ModuleEnv), [ModuleWarning])

-- | Find the file associated with a module name in the module search path.
findModule :: P.ModName -> ModuleCmd FilePath
findModule n env = runModuleM env (Base.findModule n)

-- | Load the module contained in the given file.
loadModuleByPath :: FilePath -> IO (ModuleRes T.Module)
loadModuleByPath path = do
  env <- initialModuleEnv
  runModuleM env $ do
    m <- Base.loadModuleByPath path
    setFocusedModule (T.mName m)
    return m

-- | Load the given parsed module.
loadModule :: FilePath -> P.Module -> ModuleCmd T.Module
loadModule path m env = runModuleM env $ do
  let n = P.thing (P.mName m)
  m' <- loadingModule n (Base.loadModule path m)
  setFocusedModule (T.mName m')
  return m'

-- | Check the type of an expression.
checkExpr :: P.Expr -> ModuleCmd (T.Expr,T.Schema)
checkExpr e env = runModuleM env (interactive (Base.checkExpr e))

-- | Evaluate an expression.
evalExpr :: T.Expr -> ModuleCmd E.Value
evalExpr e env = runModuleM env (interactive (Base.evalExpr e))


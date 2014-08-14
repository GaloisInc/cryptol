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
  , ExtendedEnv(..)
  , ModuleError(..), ModuleWarning(..)
  , ModuleCmd, ModuleRes
  , findModule
  , loadModuleByPath
  , loadModule
  , checkExprWith
  , evalExprWith
  , checkDeclsWith
  , evalDeclsWith
  , noPat
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
import           Cryptol.Parser.NoPat (RemovePatterns)
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
loadModule :: P.Module -> ModuleCmd T.Module
loadModule m env = runModuleM env $ do
  let n = P.thing (P.mName m)
  m' <- loadingModule n (Base.loadModule m)
  setFocusedModule (T.mName m')
  return m'

-- Extended Environments -------------------------------------------------------

-- These functions are particularly useful for interactive modes, as
-- they allow for expressions to be evaluated in an environment that
-- can extend dynamically outside of the context of a module.

-- | Check the type of an expression.
checkExprWith :: ExtendedEnv -> P.Expr -> ModuleCmd (T.Expr,T.Schema)
checkExprWith eenv e env = runModuleM env (interactive (Base.checkExprWith eenv e))

-- | Evaluate an expression.
evalExprWith :: ExtendedEnv -> T.Expr -> ModuleCmd E.Value
evalExprWith eenv e env = runModuleM env (interactive (Base.evalExprWith eenv e))

-- | Typecheck declarations.
checkDeclsWith :: ExtendedEnv -> [P.Decl] -> ModuleCmd [T.DeclGroup]
checkDeclsWith eenv ds env = runModuleM env (interactive (Base.checkDeclsWith eenv ds))

-- | Evaluate declarations and add them to the extended environment.
evalDeclsWith :: ExtendedEnv -> [T.DeclGroup] -> ModuleCmd ExtendedEnv
evalDeclsWith eenv dgs env = runModuleM env (interactive (Base.evalDeclsWith eenv dgs))

noPat :: RemovePatterns a => a -> ModuleCmd a
noPat a env = runModuleM env (interactive (Base.noPat a))

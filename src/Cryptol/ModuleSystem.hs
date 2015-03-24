-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.ModuleSystem (
    -- * Module System
    ModuleEnv(..), initialModuleEnv
  , DynamicEnv(..)
  , ModuleError(..), ModuleWarning(..)
  , ModuleCmd, ModuleRes
  , findModule
  , loadModuleByPath
  , loadModule
  , checkExpr
  , evalExpr
  , checkDecls
  , evalDecls
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
import           Cryptol.ModuleSystem.Renamer (Rename)
import qualified Cryptol.ModuleSystem.Base as Base
import qualified Cryptol.Parser.AST        as P
import           Cryptol.Parser.NoPat (RemovePatterns)
import           Cryptol.Parser.Position (HasLoc)
import qualified Cryptol.TypeCheck.AST     as T
import qualified Cryptol.TypeCheck.Depends as T


-- Public Interface ------------------------------------------------------------

type ModuleCmd a = ModuleEnv -> IO (ModuleRes a)

type ModuleRes a = (Either ModuleError (a,ModuleEnv), [ModuleWarning])

-- | Find the file associated with a module name in the module search path.
findModule :: P.ModName -> ModuleCmd FilePath
findModule n env = runModuleM env (Base.findModule n)

-- | Load the module contained in the given file.
loadModuleByPath :: FilePath -> ModuleCmd T.Module
loadModuleByPath path env = runModuleM (resetModuleEnv env) $ do
  -- unload the module if it already exists
  unloadModule path

  m <- Base.loadModuleByPath path
  setFocusedModule (T.mName m)
  return m

-- | Load the given parsed module.
loadModule :: FilePath -> P.Module -> ModuleCmd T.Module
loadModule path m env = runModuleM env $ do
  -- unload the module if it already exists
  unloadModule path

  let n = P.thing (P.mName m)
  m' <- loadingModule n (Base.loadModule path m)
  setFocusedModule (T.mName m')
  return m'

-- Extended Environments -------------------------------------------------------

-- These functions are particularly useful for interactive modes, as
-- they allow for expressions to be evaluated in an environment that
-- can extend dynamically outside of the context of a module.

-- | Check the type of an expression.
checkExpr :: P.Expr -> ModuleCmd (T.Expr,T.Schema)
checkExpr e env = runModuleM env (interactive (Base.checkExpr e))

-- | Evaluate an expression.
evalExpr :: T.Expr -> ModuleCmd E.Value
evalExpr e env = runModuleM env (interactive (Base.evalExpr e))

-- | Typecheck declarations.
checkDecls :: (HasLoc d, Rename d, T.FromDecl d) => [d] -> ModuleCmd [T.DeclGroup]
checkDecls ds env = runModuleM env (interactive (Base.checkDecls ds))

-- | Evaluate declarations and add them to the extended environment.
evalDecls :: [T.DeclGroup] -> ModuleCmd ()
evalDecls dgs env = runModuleM env (interactive (Base.evalDecls dgs))

noPat :: RemovePatterns a => a -> ModuleCmd a
noPat a env = runModuleM env (interactive (Base.noPat a))

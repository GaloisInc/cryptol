-- |
-- Module      :  Cryptol.ModuleSystem
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}

module Cryptol.ModuleSystem (
    -- * Module System
    ModuleEnv(..), initialModuleEnv
  , DynamicEnv(..)
  , ModuleError(..), ModuleWarning(..)
  , ModuleCmd, ModuleRes
  , ModuleInput(..)
  , findModule
  , loadModuleByPath
  , loadModuleByName
  , checkExpr
  , evalExpr
  , checkDecls
  , evalDecls
  , noPat
  , focusedEnv
  , getPrimMap
  , renameVar
  , renameType

    -- * Interfaces
  , Iface, IfaceG(..), IfaceParams(..), IfaceDecls(..), T.genIface
  , IfaceTySyn, IfaceDecl(..)
  ) where

import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Interface
import           Cryptol.ModuleSystem.Monad
import           Cryptol.ModuleSystem.Name (Name,PrimMap)
import qualified Cryptol.ModuleSystem.Renamer as R
import qualified Cryptol.ModuleSystem.Base as Base
import qualified Cryptol.Parser.AST        as P
import           Cryptol.Parser.Name (PName)
import           Cryptol.Parser.NoPat (RemovePatterns)
import qualified Cryptol.TypeCheck.AST     as T
import qualified Cryptol.TypeCheck.Interface as T
import qualified Cryptol.Utils.Ident as M

-- Public Interface ------------------------------------------------------------

type ModuleCmd a = ModuleInput IO -> IO (ModuleRes a)

type ModuleRes a = (Either ModuleError (a,ModuleEnv), [ModuleWarning])

getPrimMap :: ModuleCmd PrimMap
getPrimMap me = runModuleM me Base.getPrimMap

-- | Find the file associated with a module name in the module search path.
findModule :: P.ModName -> ModuleCmd ModulePath
findModule n env = runModuleM env (Base.findModule n)

-- | Load the module contained in the given file.
loadModuleByPath :: FilePath -> ModuleCmd (ModulePath,T.Module)
loadModuleByPath path minp =
  runModuleM minp{ minpModuleEnv = resetModuleEnv (minpModuleEnv minp) } $ do
    unloadModule ((InFile path ==) . lmFilePath)
    m <- Base.loadModuleByPath path
    setFocusedModule (T.mName m)
    return (InFile path,m)

-- | Load the given parsed module.
loadModuleByName :: P.ModName -> ModuleCmd (ModulePath,T.Module)
loadModuleByName n minp =
  runModuleM minp{ minpModuleEnv = resetModuleEnv (minpModuleEnv minp) } $ do
    unloadModule ((n ==) . lmName)
    (path,m') <- Base.loadModuleFrom False (FromModule n)
    setFocusedModule (T.mName m')
    return (path,m')

-- Extended Environments -------------------------------------------------------

-- These functions are particularly useful for interactive modes, as
-- they allow for expressions to be evaluated in an environment that
-- can extend dynamically outside of the context of a module.

-- | Check the type of an expression.  Give back the renamed expression, the
-- core expression, and its type schema.
checkExpr :: P.Expr PName -> ModuleCmd (P.Expr Name,T.Expr,T.Schema)
checkExpr e env = runModuleM env (interactive (Base.checkExpr e))

-- | Evaluate an expression.
evalExpr :: T.Expr -> ModuleCmd Concrete.Value
evalExpr e env = runModuleM env (interactive (Base.evalExpr e))

-- | Typecheck top-level declarations.
checkDecls :: [P.TopDecl PName] -> ModuleCmd (R.NamingEnv,[T.DeclGroup])
checkDecls ds env = runModuleM env
                  $ interactive
                  $ Base.checkDecls ds

-- | Evaluate declarations and add them to the extended environment.
evalDecls :: [T.DeclGroup] -> ModuleCmd ()
evalDecls dgs env = runModuleM env (interactive (Base.evalDecls dgs))

noPat :: RemovePatterns a => a -> ModuleCmd a
noPat a env = runModuleM env (interactive (Base.noPat a))

-- | Rename a *use* of a value name. The distinction between uses and
-- binding is used to keep track of dependencies.
renameVar :: R.NamingEnv -> PName -> ModuleCmd Name
renameVar names n env = runModuleM env $ interactive $
  Base.rename M.interactiveName names (R.renameVar R.NameUse n)

-- | Rename a *use* of a type name. The distinction between uses and
-- binding is used to keep track of dependencies.
renameType :: R.NamingEnv -> PName -> ModuleCmd Name
renameType names n env = runModuleM env $ interactive $
  Base.rename M.interactiveName names (R.renameType R.NameUse n)

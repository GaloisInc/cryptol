-- |
-- Module      :  Cryptol.ModuleSystem
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}

module Cryptol.ModuleSystem (
    -- * Module System
    ModuleEnv(..), initialModuleEnv, makeRelativeToSearchPath
  , DynamicEnv(..)
  , ModuleError(..), ModuleWarning(..)
  , ModuleCmd, ModuleRes
  , ModuleInput(..)
  , findModule
  , loadModuleByPath
  , loadModuleByName
  , checkModuleByPath
  , checkExpr
  , evalExpr
  , benchmarkExpr
  , checkDecls
  , evalDecls
  , noPat
  , focusedEnv
  , getPrimMap
  , renameVar
  , renameType
  , setFocusedModule
  , Base.renameImpNameInCurrentEnv
  , impNameTopModule

    -- * Interfaces
  , Iface, IfaceG(..), IfaceDecls(..), T.genIface, IfaceDecl(..)

    -- * Dependencies
  , getFileDependencies
  , getModuleDependencies
  ) where

import qualified Control.Exception as X
import Data.Map (Map)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import System.Directory (canonicalizePath, makeAbsolute)
import System.FilePath
  ( isAbsolute, makeRelative, normalise, splitDirectories )

import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Interface
import           Cryptol.ModuleSystem.Monad
import           Cryptol.ModuleSystem.Name (Name,PrimMap,nameTopModule)
import qualified Cryptol.ModuleSystem.Renamer as R
import qualified Cryptol.ModuleSystem.Base as Base
import qualified Cryptol.Parser.AST        as P
import           Cryptol.Parser.Name (PName)
import           Cryptol.Parser.NoPat (RemovePatterns)
import qualified Cryptol.TypeCheck.AST     as T
import qualified Cryptol.TypeCheck.Interface as T
import           Cryptol.Utils.Benchmark (BenchmarkStats)
import qualified Cryptol.Utils.Ident as M

-- Public Interface ------------------------------------------------------------

type ModuleCmd a = ModuleInput IO -> IO (ModuleRes a)

type ModuleRes a = (Either ModuleError (a,ModuleEnv), [ModuleWarning])

-- | Make an absolute filename relative to the first matching entry in the
-- module search path. If the file is outside the search path, leave it
-- absolute.
makeRelativeToSearchPath :: ModuleEnv -> FilePath -> IO FilePath
makeRelativeToSearchPath me file =
  do roots <- mapM canonicalSearchRoot (meSearchPath me)
     pure (fromMaybe file' (listToMaybe (mapMaybe relativeTo roots)))
  where
  file' = normalise file

  canonicalSearchRoot path =
    X.catch (canonicalizePath path) fallback
    where
    fallback :: X.IOException -> IO FilePath
    fallback _ = makeAbsolute path

  relativeTo root =
    let relative = normalise (makeRelative root file')
    in case splitDirectories relative of
         ".." : _ -> Nothing
         _ | isAbsolute relative -> Nothing
           | otherwise -> Just relative

getPrimMap :: ModuleCmd PrimMap
getPrimMap me = runModuleM me Base.getPrimMap

-- | Find the file associated with a module name in the module search path.
findModule :: P.ModName -> ModuleCmd ModulePath
findModule n env = runModuleM env (Base.findModule (FromModule n) n)

-- | Load the module contained in the given file.
loadModuleByPath :: FilePath -> ModuleCmd (ModulePath,T.TCTopEntity)
loadModuleByPath path minp = do
  moduleEnv' <- resetModuleEnv $ minpModuleEnv minp
  runModuleM minp{ minpModuleEnv = moduleEnv' } $ do
    m <- Base.loadModuleByPath True path
    setFocusedModule (P.ImpTop (T.tcTopEntitytName m))
    return (InFile path,m)

-- | Load the given parsed module.
loadModuleByName :: P.ModName -> ModuleCmd (ModulePath,T.TCTopEntity)
loadModuleByName n minp = do
  moduleEnv' <- resetModuleEnv $ minpModuleEnv minp
  runModuleM minp{ minpModuleEnv = moduleEnv' } $ do
    (path,m') <- Base.loadModuleFrom False (FromModule n)
    setFocusedModule (P.ImpTop (T.tcTopEntitytName m'))
    return (path,m')

-- | Parse and typecheck a module, but don't evaluate or change the environment.
checkModuleByPath :: FilePath -> ModuleCmd (ModulePath, T.TCTopEntity)
checkModuleByPath path minp = do
  (res, warns) <- runModuleM minp $ Base.loadModuleByPath False path
  -- restore the old environment
  let res1 = do (x,_newEnv) <- res
                pure ((InFile path, x), minpModuleEnv minp)
  pure (res1, warns)

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

-- | Benchmark an expression.
benchmarkExpr :: Double -> T.Expr -> ModuleCmd BenchmarkStats
benchmarkExpr period e env =
  runModuleM env (interactive (Base.benchmarkExpr period e))

-- | Typecheck top-level declarations.
checkDecls :: [P.TopDecl PName] -> ModuleCmd (R.NamingEnv,[T.DeclGroup], Map Name T.TySyn)
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
  Base.rename M.interactiveName names (R.resolveNameUse M.NSValue n)

-- | Rename a *use* of a type name. The distinction between uses and
-- binding is used to keep track of dependencies.
renameType :: R.NamingEnv -> PName -> ModuleCmd Name
renameType names n env = runModuleM env $ interactive $
  Base.rename M.interactiveName names (R.resolveNameUse M.NSType n)

--------------------------------------------------------------------------------
-- Dependencies


-- | Get information about the dependencies of a file.
getFileDependencies :: FilePath -> ModuleCmd (ModulePath, FileInfo)
getFileDependencies f env = runModuleM env (Base.findDepsOf (InFile f))

-- | Get information about the dependencies of a module.
getModuleDependencies :: M.ModName -> ModuleCmd (ModulePath, FileInfo)
getModuleDependencies m env = runModuleM env (Base.findDepsOfModule m)

--------------------------------------------------------------------------------
-- ImpName utilities

impNameTopModule :: P.ImpName Name -> M.ModName
impNameTopModule impName =
    case impName of
      P.ImpTop m -> m
      P.ImpNested n -> nameTopModule n

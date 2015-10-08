-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.ModuleSystem.Base where

import Cryptol.ModuleSystem.Env (DynamicEnv(..), deIfaceDecls)
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Monad
import Cryptol.ModuleSystem.Name (preludeName)
import Cryptol.ModuleSystem.Env (lookupModule, LoadedModule(..)
                                , meCoreLint, CoreLint(..))
import qualified Cryptol.Eval                 as E
import qualified Cryptol.Eval.Value           as E
import qualified Cryptol.ModuleSystem.Renamer as R
import qualified Cryptol.Parser               as P
import qualified Cryptol.Parser.Unlit         as P
import Cryptol.Parser.AST as P
import Cryptol.Parser.NoPat (RemovePatterns(removePatterns))
import Cryptol.Parser.NoInclude (removeIncludesModule)
import Cryptol.Parser.Position (HasLoc(..), Range, emptyRange)
import qualified Cryptol.TypeCheck     as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Depends as T
import qualified Cryptol.TypeCheck.PP as T
import qualified Cryptol.TypeCheck.Sanity as TcSanity
import Cryptol.Utils.PP (pretty)
import Cryptol.Utils.Panic (panic)

import Cryptol.Prelude (writePreludeContents)

import Cryptol.Transform.MonoValues

import Control.DeepSeq
import qualified Control.Exception as X
import Control.Monad (unless)
import Data.Function (on)
import Data.List (nubBy)
import Data.Maybe (mapMaybe,fromMaybe)
import Data.Monoid ((<>))
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as T
import System.Directory (doesFileExist)
import System.FilePath ( addExtension
                       , isAbsolute
                       , joinPath
                       , (</>)
                       , takeDirectory
                       , takeFileName
                       )
import qualified System.IO.Error as IOE
import qualified Data.Map as Map

import Prelude ()
import Prelude.Compat

-- Renaming --------------------------------------------------------------------

rename :: R.Rename a => R.NamingEnv -> a -> ModuleM a
rename env a = do
  renamerWarnings ws
  case res of
    Right r   -> return r
    Left errs -> renamerErrors errs
  where
  (res,ws) = R.runRenamer env (R.rename a)

-- | Rename a module in the context of its imported modules.
renameModule :: P.Module -> ModuleM P.Module
renameModule m = do
  iface <- importIfaces (map thing (P.mImports m))

  let menv    = R.namingEnv m
      (es,ws) = R.checkNamingEnv menv

  renamerWarnings ws
  unless (null es) (renamerErrors es)

  -- explicitly shadow the imported environment with the local environment
  rename (menv `R.shadowing` R.namingEnv iface) m

-- | Rename an expression in the context of the focused module.
renameExpr :: P.Expr -> ModuleM P.Expr
renameExpr e = do
  (env,_) <- getFocusedEnv
  denv <- getDynEnv
  rename (deNames denv `R.shadowing` R.namingEnv env) e

-- | Rename declarations in the context of the focused module.
renameDecls :: (R.Rename d, T.FromDecl d) => [d] -> ModuleM [d]
renameDecls ds = do
  (env,_) <- getFocusedEnv
  denv <- getDynEnv
  rename (deNames denv `R.shadowing` R.namingEnv env) ds

-- NoPat -----------------------------------------------------------------------

-- | Run the noPat pass.
noPat :: RemovePatterns a => a -> ModuleM a
noPat a = do
  let (a',errs) = removePatterns a
  unless (null errs) (noPatErrors errs)
  return a'


-- Parsing ---------------------------------------------------------------------

parseModule :: FilePath -> ModuleM P.Module
parseModule path = do

  e <- io $ X.try $ do
    bytes <- T.readFile path
    return $!! bytes
  bytes <- case (e :: Either X.IOException Text) of
    Right bytes -> return bytes
    Left exn | IOE.isDoesNotExistError exn -> cantFindFile path
             | otherwise                   -> otherIOError path exn

  let cfg = P.defaultConfig
              { P.cfgSource  = path
              , P.cfgPreProc = P.guessPreProc path
              }
  case P.parseModule cfg bytes of
    Right pm -> return pm
    Left err -> moduleParseError path err


-- Modules ---------------------------------------------------------------------

-- | Load a module by its path.
loadModuleByPath :: FilePath -> ModuleM T.Module
loadModuleByPath path = withPrependedSearchPath [ takeDirectory path ] $ do
  let fileName = takeFileName path
  -- path' is the resolved, absolute path
  path' <- findFile fileName
  pm <- parseModule path'
  let n = thing (P.mName pm)

  -- Check whether this module name has already been loaded from a different file
  env <- getModuleEnv
  case lookupModule n env of
    Nothing -> loadingModule n (loadModule path' pm)
    Just lm
      | path' == loaded -> return (lmModule lm)
      | otherwise       -> duplicateModuleName n path' loaded
      where loaded = lmFilePath lm


-- | Load the module specified by an import.
loadImport :: Located P.Import -> ModuleM ()
loadImport li = do

  let i = thing li
      n = P.iModule i

  alreadyLoaded <- isLoaded n
  unless alreadyLoaded $
    do path <- findModule n
       pm   <- parseModule path
       loadingImport li $ do

         -- make sure that this module is the one we expect
         unless (n == thing (P.mName pm)) (moduleNameMismatch n (mName pm))

         _ <- loadModule path pm
         return ()

-- | Load dependencies, typecheck, and add to the eval environment.
loadModule :: FilePath -> P.Module -> ModuleM T.Module
loadModule path pm = do

  let pm' = addPrelude pm
  loadDeps pm'

  -- XXX make it possible to configure output
  io (putStrLn ("Loading module " ++ pretty (P.thing (P.mName pm'))))

  tcm <- checkModule path pm'

  -- extend the eval env
  modifyEvalEnv (E.moduleEnv tcm)

  loadedModule path tcm

  return tcm


-- | Rewrite an import declaration to be of the form:
--
-- > import foo as foo [ [hiding] (a,b,c) ]
fullyQualified :: P.Import -> P.Import
fullyQualified i = i { iAs = Just (iModule i) }

-- | Process the interface specified by an import.
importIface :: P.Import -> ModuleM Iface
importIface i = (fst . interpImport i) `fmap` getIface (T.iModule i)

-- | Load a series of interfaces, merging their public interfaces.
importIfaces :: [P.Import] -> ModuleM IfaceDecls
importIfaces is = foldMap ifPublic `fmap` mapM importIface is

moduleFile :: ModName -> String -> FilePath
moduleFile n = addExtension (joinPath (P.unModName n))

-- | Discover a module.
findModule :: ModName -> ModuleM FilePath
findModule n = do
  paths <- getSearchPath
  loop (possibleFiles paths)
  where
  loop paths = case paths of

    path:rest -> do
      b <- io (doesFileExist path)
      if b then return path else loop rest

    [] -> handleNotFound

  handleNotFound =
    case n of
      m | m == preludeName -> writePreludeContents
      _ -> moduleNotFound n =<< getSearchPath

  -- generate all possible search paths
  possibleFiles paths = do
    path <- paths
    ext  <- P.knownExts
    return (path </> moduleFile n ext)

-- | Discover a file. This is distinct from 'findModule' in that we
-- assume we've already been given a particular file name.
findFile :: FilePath -> ModuleM FilePath
findFile path | isAbsolute path = do
  -- No search path checking for absolute paths
  b <- io (doesFileExist path)
  if b then return path else cantFindFile path
findFile path = do
  paths <- getSearchPath
  loop (possibleFiles paths)
  where
  loop paths = case paths of
    path':rest -> do
      b <- io (doesFileExist path')
      if b then return path' else loop rest
    [] -> cantFindFile path
  possibleFiles paths = map (</> path) paths

-- | Add the prelude to the import list if it's not already mentioned.
addPrelude :: P.Module -> P.Module
addPrelude m
  | preludeName == P.thing (P.mName m) = m
  | preludeName `elem` importedMods    = m
  | otherwise                          = m { mImports = importPrelude : mImports m }
  where
  importedMods  = map (P.iModule . P.thing) (P.mImports m)
  importPrelude = P.Located
    { P.srcRange = emptyRange
    , P.thing    = P.Import
      { iModule    = preludeName
      , iAs        = Nothing
      , iSpec      = Nothing
      }
    }

-- | Load the dependencies of a module into the environment.
loadDeps :: Module -> ModuleM ()
loadDeps m
  | null needed = return ()
  | otherwise   = mapM_ load needed
  where
  needed  = nubBy ((==) `on` P.iModule . thing) (P.mImports m)
  load mn = loadImport mn


-- Type Checking ---------------------------------------------------------------

-- | Typecheck a single expression.
checkExpr :: P.Expr -> ModuleM (P.Expr,T.Expr,T.Schema)
checkExpr e = do
  npe <- noPat e
  denv <- getDynEnv
  re  <- renameExpr npe
  env <- getQualifiedEnv
  let env' = env <> deIfaceDecls denv
      act  = TCAction { tcAction = T.tcExpr, tcLinter = exprLinter }
  (te,s) <- typecheck act re env'
  return (re,te,s)

-- | Typecheck a group of declarations.
checkDecls :: (HasLoc d, R.Rename d, T.FromDecl d) => [d] -> ModuleM [T.DeclGroup]
checkDecls ds = do
  -- nopat must already be run
  rds <- renameDecls ds
  denv <- getDynEnv
  env <- getQualifiedEnv
  let env' = env <> deIfaceDecls denv
      act  = TCAction { tcAction = T.tcDecls, tcLinter = declsLinter }
  typecheck act rds env'

-- | Typecheck a module.
checkModule :: FilePath -> P.Module -> ModuleM T.Module
checkModule path m = do
  -- remove includes first
  e   <- io (removeIncludesModule path m)
  nim <- case e of
           Right nim  -> return nim
           Left ierrs -> noIncludeErrors ierrs

  -- remove pattern bindings
  npm <- noPat nim

  -- rename everything
  scm <- renameModule npm

  let act = TCAction { tcAction = T.tcModule
                     , tcLinter = moduleLinter (P.thing (P.mName m)) }
  -- typecheck
  tcm <- typecheck act scm =<< importIfacesTc (map thing (P.mImports scm))

  return (Cryptol.Transform.MonoValues.rewModule tcm)

data TCLinter o = TCLinter
  { lintCheck ::
      o -> T.InferInput -> Either TcSanity.Error [TcSanity.ProofObligation]
  , lintModule :: Maybe P.ModName
  }


exprLinter :: TCLinter (T.Expr, T.Schema)
exprLinter = TCLinter
  { lintCheck = \(e',s) i ->
      case TcSanity.tcExpr (T.inpVars i) e' of
        Left err     -> Left err
        Right (s1,os)
          | TcSanity.same s s1  -> Right os
          | otherwise -> Left (TcSanity.TypeMismatch s s1)
  , lintModule = Nothing
  }

declsLinter :: TCLinter [ T.DeclGroup ]
declsLinter = TCLinter
  { lintCheck = \ds' i -> case TcSanity.tcDecls (T.inpVars i) ds' of
                            Left err -> Left err
                            Right os -> Right os

  , lintModule = Nothing
  }

moduleLinter :: P.ModName -> TCLinter T.Module
moduleLinter m = TCLinter
  { lintCheck   = \m' i -> case TcSanity.tcModule (T.inpVars i) m' of
                            Left err -> Left err
                            Right os -> Right os
  , lintModule  = Just m
  }


data TCAction i o = TCAction
  { tcAction :: i -> T.InferInput -> IO (T.InferOutput o)
  , tcLinter :: TCLinter o
  }

typecheck :: HasLoc i => TCAction i o -> i -> IfaceDecls -> ModuleM o
typecheck act i env = do

  let range = fromMaybe emptyRange (getLoc i)
  input <- genInferInput range env
  out   <- io (tcAction act i input)

  case out of

    T.InferOK warns seeds o ->
      do setNameSeeds seeds
         typeCheckWarnings warns
         menv <- getModuleEnv
         case meCoreLint menv of
           NoCoreLint -> return ()
           CoreLint   -> case lintCheck (tcLinter act) o input of
                           Right as -> io $ mapM_ (print . T.pp) as
                           Left err -> panic "Core lint failed:" [show err]
         return o

    T.InferFailed warns errs ->
      do typeCheckWarnings warns
         typeCheckingFailed errs

-- | Process a list of imports, producing an aggregate interface suitable for use
-- when typechecking.
importIfacesTc :: [P.Import] -> ModuleM IfaceDecls
importIfacesTc is =
  mergePublic `fmap` mapM (importIface . fullyQualified) is
  where
  mergePublic = foldMap ifPublic

-- | Generate input for the typechecker.
genInferInput :: Range -> IfaceDecls -> ModuleM T.InferInput
genInferInput r env = do
  seeds <- getNameSeeds
  monoBinds <- getMonoBinds
  cfg <- getSolverConfig

  -- TODO: include the environment needed by the module
  return T.InferInput
    { T.inpRange     = r
    , T.inpVars      = Map.map ifDeclSig (filterEnv ifDecls)
    , T.inpTSyns     =                    filterEnv ifTySyns
    , T.inpNewtypes  =                    filterEnv ifNewtypes
    , T.inpNameSeeds = seeds
    , T.inpMonoBinds = monoBinds
    , T.inpSolverConfig = cfg
    }
  where
  -- at this point, the names used in the aggregate interface should be
  -- unique
  keepOne :: (QName,[a]) -> Maybe (QName,a)
  keepOne (qn,syns) = case syns of
    [syn] -> Just (qn,syn)
    _     -> Nothing

  -- keep symbols without duplicates.  the renamer would have caught
  -- duplication already, so this is safe.
  filterEnv p = Map.fromList (mapMaybe keepOne (Map.toList (p env)))


-- Evaluation ------------------------------------------------------------------

evalExpr :: T.Expr -> ModuleM E.Value
evalExpr e = do
  env <- getEvalEnv
  denv <- getDynEnv
  return (E.evalExpr (env <> deEnv denv) e)

evalDecls :: [T.DeclGroup] -> ModuleM ()
evalDecls dgs = do
  env <- getEvalEnv
  denv <- getDynEnv
  let env' = env <> deEnv denv
      denv' = denv { deDecls = deDecls denv ++ dgs
                   , deEnv = E.evalDecls dgs env'
                   }
  setDynEnv denv'

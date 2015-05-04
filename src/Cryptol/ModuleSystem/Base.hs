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
import Cryptol.ModuleSystem.Env (lookupModule, LoadedModule(..))
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
import Cryptol.Utils.PP (pretty)

import Cryptol.Prelude (writePreludeContents)

import Cryptol.Transform.MonoValues

import Control.DeepSeq
import qualified Control.Exception as X
import Control.Monad (unless)
import Data.Function (on)
import Data.List (nubBy)
import Data.Maybe (mapMaybe,fromMaybe)
import Data.Monoid ((<>))
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

#if __GLASGOW_HASKELL__ < 710
import Data.Foldable (foldMap)
#endif

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
  env <- getFocusedEnv
  denv <- getDynEnv
  rename (deNames denv `R.shadowing` R.namingEnv env) e

-- | Rename declarations in the context of the focused module.
renameDecls :: (R.Rename d, T.FromDecl d) => [d] -> ModuleM [d]
renameDecls ds = do
  env <- getFocusedEnv
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
    bytes <- readFile path
    return $!! bytes
  bytes <- case (e :: Either X.IOException String) of
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

  tcm <- checkModule pm'

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
importIface i = interpImport i `fmap` getIface (T.iModule i)

-- | Load a series of interfaces, merging their public interfaces.
importIfaces :: [P.Import] -> ModuleM IfaceDecls
importIfaces is = foldMap ifPublic `fmap` mapM importIface is

moduleFile :: ModName -> String -> FilePath
moduleFile (ModName ns) = addExtension (joinPath ns)

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

preludeName :: P.ModName
preludeName  = P.ModName ["Cryptol"]

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
checkExpr :: P.Expr -> ModuleM (T.Expr,T.Schema)
checkExpr e = do
  npe <- noPat e
  denv <- getDynEnv
  re  <- renameExpr npe
  env <- getQualifiedEnv
  let env' = env <> deIfaceDecls denv
  typecheck T.tcExpr re env'

-- | Typecheck a group of declarations.
checkDecls :: (HasLoc d, R.Rename d, T.FromDecl d) => [d] -> ModuleM [T.DeclGroup]
checkDecls ds = do
  -- nopat must already be run
  rds <- renameDecls ds
  denv <- getDynEnv
  env <- getQualifiedEnv
  let env' = env <> deIfaceDecls denv
  typecheck T.tcDecls rds env'

-- | Typecheck a module.
checkModule :: P.Module -> ModuleM T.Module
checkModule m = do
  -- remove includes first
  e   <- io (removeIncludesModule m)
  nim <- case e of
           Right nim  -> return nim
           Left ierrs -> noIncludeErrors ierrs

  -- remove pattern bindings
  npm <- noPat nim

  -- rename everything
  scm <- renameModule npm

  -- typecheck
  tcm <- typecheck T.tcModule scm =<< importIfacesTc (map thing (P.mImports scm))

  return (Cryptol.Transform.MonoValues.rewModule tcm)


type TCAction i o = i -> T.InferInput -> IO (T.InferOutput o)

typecheck :: HasLoc i => TCAction i o -> i -> IfaceDecls -> ModuleM o
typecheck action i env = do

  let range = fromMaybe emptyRange (getLoc i)
  input <- genInferInput range env
  out   <- io (action i input)

  case out of

    T.InferOK warns seeds o ->
      do setNameSeeds seeds
         typeCheckWarnings warns
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

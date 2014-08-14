-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.ModuleSystem.Base where

import Cryptol.ModuleSystem.Env (ExtendedEnv(..))
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Monad
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
import Cryptol.Utils.PP (pretty)

import Cryptol.Transform.MonoValues

import qualified Control.Exception as X
import Control.Monad (unless)
import Data.Foldable (foldMap)
import Data.Function (on)
import Data.List (nubBy)
import Data.Maybe (mapMaybe,fromMaybe)
import Data.Monoid ((<>), mconcat)
import System.Directory (doesFileExist)
import System.FilePath (addExtension,joinPath,(</>))
import qualified Data.Map as Map


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
  rename (R.namingEnv env) e

-- | Rename an expression in the context of the focused module and an
-- extended environment.
renameExprWith :: ExtendedEnv -> P.Expr -> ModuleM P.Expr
renameExprWith eenv e = do
  env <- getFocusedEnv
  rename (eeNames eenv `R.shadowing` R.namingEnv env) e

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

  e <- io (X.try (readFile path) :: IO (Either X.IOException String))
  bytes <- case e of
    Right bytes -> return bytes
    Left _      -> cantFindFile path

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
loadModuleByPath path = do
  pm <- parseModule path
  let n = thing (P.mName pm)
  loadingModule n (loadModule pm)

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

         _ <- loadModule pm
         return ()

-- | Load dependencies, typecheck, and add to the eval environment.
loadModule :: P.Module -> ModuleM T.Module
loadModule pm = do

  let pm' = addPrelude pm
  loadDeps pm'

  -- XXX make it possible to configure output
  io (putStrLn ("Loading module " ++ pretty (P.thing (P.mName pm'))))

  tcm <- checkModule pm'

  -- extend the eval env
  modifyEvalEnv (E.moduleEnv tcm)

  loadedModule tcm

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
--
-- TODO: extend this with a search path.
findModule :: ModName -> ModuleM FilePath
findModule n = do
  paths <- getSearchPath
  loop (possibleFiles paths)
  where
  loop paths = case paths of

    path:rest -> do
      b <- io (doesFileExist path)
      if b then return path else loop rest

    [] -> moduleNotFound n =<< getSearchPath

  -- generate all possible search paths
  possibleFiles paths = do
    path <- paths
    ext  <- P.knownExts
    return (path </> moduleFile n ext)

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
  re  <- renameExpr npe
  typecheck T.tcExpr re =<< getQualifiedEnv

-- | Typecheck a single expression in an extended environment.
checkExprWith :: ExtendedEnv -> P.Expr -> ModuleM (T.Expr,T.Schema)
checkExprWith eenv e = do
  npe <- noPat e
  re  <- renameExprWith eenv npe
  env <- getQualifiedEnv
  let env' = env <> eeIfaceDecls eenv
  typecheck T.tcExpr re env'

eeIfaceDecls :: ExtendedEnv -> IfaceDecls
eeIfaceDecls EEnv { eeDecls = dgs } =
  mconcat [ IfaceDecls
            { ifTySyns   = Map.empty
            , ifNewtypes = Map.empty
            , ifDecls    = Map.singleton (ifDeclName ifd) [ifd]
            }
          | decl <- concatMap T.groupDecls dgs
          , let ifd = mkIfaceDecl decl
          ]

-- | Typecheck a group of declarations in an extended environment.
checkDeclsWith :: ExtendedEnv -> [P.Decl] -> ModuleM [T.DeclGroup]
checkDeclsWith eenv ds = do
  -- nopat must already be run
  rds <- rename (eeNames eenv) ds
  env <- getQualifiedEnv
  let env' = env <> eeIfaceDecls eenv
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

-- | Process a list of imports, producing an aggreate interface suitable for use
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

  -- TODO: include the environment needed by the module
  return T.InferInput
    { T.inpRange     = r
    , T.inpVars      = Map.map ifDeclSig (filterEnv ifDecls)
    , T.inpTSyns     =                    filterEnv ifTySyns
    , T.inpNewtypes  =                    filterEnv ifNewtypes
    , T.inpNameSeeds = seeds
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
  return (E.evalExpr env e)

evalExprWith :: ExtendedEnv -> T.Expr -> ModuleM E.Value
evalExprWith eenv e = do
  env <- getEvalEnv
  return (E.evalExpr (env <> eeEnv eenv) e)

-- | Evaluate typechecked declarations in an extended environment. The
-- result of this is a new environment whose 'EvalEnv' is extended
-- with the new declarations and their values.
evalDeclsWith :: ExtendedEnv -> [T.DeclGroup] -> ModuleM ExtendedEnv
evalDeclsWith eenv dgs = do
  env <- getEvalEnv
  let env' = env <> eeEnv eenv
  return $ eenv { eeDecls = eeDecls eenv ++ dgs, eeEnv = E.evalDecls dgs env' }

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}

module Cryptol.ModuleSystem.Base where

import Cryptol.ModuleSystem.Env (DynamicEnv(..), deIfaceDecls)
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Monad
import Cryptol.ModuleSystem.Name (Name,liftSupply,PrimMap)
import Cryptol.ModuleSystem.Env (lookupModule, LoadedModule(..)
                                , meCoreLint, CoreLint(..))
import qualified Cryptol.Eval                 as E
import qualified Cryptol.Eval.Value           as E
import           Cryptol.Prims.Eval ()
import qualified Cryptol.ModuleSystem.NamingEnv as R
import qualified Cryptol.ModuleSystem.Renamer as R
import qualified Cryptol.Parser               as P
import qualified Cryptol.Parser.Unlit         as P
import Cryptol.Parser.AST as P
import Cryptol.Parser.NoPat (RemovePatterns(removePatterns))
import Cryptol.Parser.NoInclude (removeIncludesModule)
import Cryptol.Parser.Position (HasLoc(..), Range, emptyRange)
import qualified Cryptol.TypeCheck     as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.PP as T
import qualified Cryptol.TypeCheck.Sanity as TcSanity
import Cryptol.Utils.Ident (preludeName,interactiveName,unpackModName)
import Cryptol.Utils.PP (pretty)
import Cryptol.Utils.Panic (panic)

import Cryptol.Prelude (writePreludeContents)

import Cryptol.Transform.MonoValues (rewModule)

import Control.DeepSeq
import qualified Control.Exception as X
import Control.Monad (unless)
import Data.Function (on)
import Data.List (nubBy)
import Data.Maybe (fromMaybe)
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

rename :: ModName -> R.NamingEnv -> R.RenameM a -> ModuleM a
rename modName env m = do
  (res,ws) <- liftSupply $ \ supply ->
    case R.runRenamer supply modName env m of
      (Right (a,supply'),ws) -> ((Right a,ws),supply')
      (Left errs,ws)         -> ((Left errs,ws),supply)

  renamerWarnings ws
  case res of
    Right r   -> return r
    Left errs -> renamerErrors errs

-- | Rename a module in the context of its imported modules.
renameModule :: P.Module PName
             -> ModuleM (IfaceDecls,R.NamingEnv,P.Module Name)
renameModule m = do
  (decls,menv) <- importIfaces (map thing (P.mImports m))
  (declsEnv,rm) <- rename (thing (mName m)) menv (R.renameModule m)
  return (decls,declsEnv,rm)


-- NoPat -----------------------------------------------------------------------

-- | Run the noPat pass.
noPat :: RemovePatterns a => a -> ModuleM a
noPat a = do
  let (a',errs) = removePatterns a
  unless (null errs) (noPatErrors errs)
  return a'


-- Parsing ---------------------------------------------------------------------

parseModule :: FilePath -> ModuleM (P.Module PName)
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
loadModule :: FilePath -> P.Module PName -> ModuleM T.Module
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

-- | Find the interface referenced by an import, and generate the naming
-- environment that it describes.
importIface :: P.Import -> ModuleM (IfaceDecls,R.NamingEnv)
importIface imp =
  do Iface { .. } <- getIface (T.iModule imp)
     return (ifPublic, R.interpImport imp ifPublic)

-- | Load a series of interfaces, merging their public interfaces.
importIfaces :: [P.Import] -> ModuleM (IfaceDecls,R.NamingEnv)
importIfaces is = mconcat `fmap` mapM importIface is

moduleFile :: ModName -> String -> FilePath
moduleFile n = addExtension (joinPath (unpackModName n))

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
addPrelude :: P.Module PName -> P.Module PName
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
loadDeps :: P.Module name -> ModuleM ()
loadDeps m
  | null needed = return ()
  | otherwise   = mapM_ load needed
  where
  needed  = nubBy ((==) `on` P.iModule . thing) (P.mImports m)
  load mn = loadImport mn


-- Type Checking ---------------------------------------------------------------

-- | Load the local environment, which consists of the environment for the
-- currently opened module, shadowed by the dynamic environment.
getLocalEnv :: ModuleM (IfaceDecls,R.NamingEnv)
getLocalEnv  =
  do (decls,fNames,_) <- getFocusedEnv
     denv             <- getDynEnv
     let dynDecls = deIfaceDecls denv
     return (dynDecls `mappend` decls, deNames denv `R.shadowing` fNames)

-- | Typecheck a single expression, yielding a renamed parsed expression,
-- typechecked core expression, and a type schema.
checkExpr :: P.Expr PName -> ModuleM (P.Expr Name,T.Expr,T.Schema)
checkExpr e = do

  (decls,names) <- getLocalEnv

  -- run NoPat
  npe <- noPat e

  -- rename the expression with dynamic names shadowing the opened environment
  re  <- rename interactiveName names (R.rename npe)

  -- merge the dynamic and opened environments for typechecking
  prims <- getPrimMap
  let act  = TCAction { tcAction = T.tcExpr, tcLinter = exprLinter
                      , tcPrims = prims }
  (te,s) <- typecheck act re decls

  return (re,te,s)

-- | Typecheck a group of declarations.
--
-- INVARIANT: This assumes that NoPat has already been run on the declarations.
checkDecls :: [P.TopDecl PName] -> ModuleM (R.NamingEnv,[T.DeclGroup])
checkDecls ds = do
  (decls,names) <- getLocalEnv

  -- introduce names for the declarations before renaming them
  declsEnv <- liftSupply (R.namingEnv' (map (R.InModule interactiveName) ds))
  rds <- rename interactiveName (declsEnv `R.shadowing` names)
             (traverse R.rename ds)

  prims <- getPrimMap
  let act  = TCAction { tcAction = T.tcDecls, tcLinter = declsLinter
                      , tcPrims = prims }
  ds' <- typecheck act rds decls
  return (declsEnv,ds')

-- | Generate the primitive map. If the prelude is currently being loaded, this
-- should be generated directly from the naming environment given to the renamer
-- instead.
getPrimMap :: ModuleM PrimMap
getPrimMap  =
  do env <- getModuleEnv
     case lookupModule preludeName env of
       Just lm -> return (ifacePrimMap (lmInterface lm))
       Nothing -> panic "Cryptol.ModuleSystem.Base.getPrimMap"
                  [ "Unable to find the prelude" ]

-- | Typecheck a module.
checkModule :: FilePath -> P.Module PName -> ModuleM T.Module
checkModule path m = do
  -- remove includes first
  e   <- io (removeIncludesModule path m)
  nim <- case e of
           Right nim  -> return nim
           Left ierrs -> noIncludeErrors ierrs

  -- remove pattern bindings
  npm <- noPat nim

  -- rename everything
  (tcEnv,declsEnv,scm) <- renameModule npm

  -- when generating the prim map for the typechecker, if we're checking the
  -- prelude, we have to generate the map from the renaming environment, as we
  -- don't have the interface yet.
  prims <- if thing (mName m) == preludeName
              then return (R.toPrimMap declsEnv)
              else getPrimMap

  -- typecheck
  let act = TCAction { tcAction = T.tcModule
                     , tcLinter = moduleLinter (P.thing (P.mName m))
                     , tcPrims  = prims }
  tcm <- typecheck act scm tcEnv

  liftSupply (`rewModule` tcm)

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
  , tcPrims  :: PrimMap
  }

typecheck :: (Show i, Show o, HasLoc i) => TCAction i o -> i -> IfaceDecls -> ModuleM o
typecheck act i env = do

  let range = fromMaybe emptyRange (getLoc i)
  input <- genInferInput range (tcPrims act) env
  out   <- io (tcAction act i input)

  case out of

    T.InferOK warns seeds supply' o ->
      do setNameSeeds seeds
         setSupply supply'
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

-- | Generate input for the typechecker.
genInferInput :: Range -> PrimMap -> IfaceDecls -> ModuleM T.InferInput
genInferInput r prims env = do
  seeds <- getNameSeeds
  monoBinds <- getMonoBinds
  cfg <- getSolverConfig
  supply <- getSupply
  searchPath <- getSearchPath

  -- TODO: include the environment needed by the module
  return T.InferInput
    { T.inpRange     = r
    , T.inpVars      = Map.map ifDeclSig (ifDecls env)
    , T.inpTSyns     = ifTySyns env
    , T.inpNewtypes  = ifNewtypes env
    , T.inpNameSeeds = seeds
    , T.inpMonoBinds = monoBinds
    , T.inpSolverConfig = cfg
    , T.inpSearchPath = searchPath
    , T.inpSupply    = supply
    , T.inpPrimNames = prims
    }


-- Evaluation ------------------------------------------------------------------

evalExpr :: T.Expr -> ModuleM E.Value
evalExpr e = do
  env <- getEvalEnv
  denv <- getDynEnv
  io $ E.runEval $ (E.evalExpr (env <> deEnv denv) e)

evalDecls :: [T.DeclGroup] -> ModuleM ()
evalDecls dgs = do
  env <- getEvalEnv
  denv <- getDynEnv
  let env' = env <> deEnv denv
  deEnv' <- io $ E.runEval $ E.evalDecls dgs env'
  let denv' = denv { deDecls = deDecls denv ++ dgs
                   , deEnv = deEnv'
                   }
  setDynEnv denv'

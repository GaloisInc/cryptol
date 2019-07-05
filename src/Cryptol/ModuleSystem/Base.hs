-- |
-- Module      :  Cryptol.ModuleSystem.Base
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This is the main driver---it provides entry points for the
-- various passes.

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}

module Cryptol.ModuleSystem.Base where

import Cryptol.ModuleSystem.Env (DynamicEnv(..), deIfaceDecls)
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Monad
import Cryptol.ModuleSystem.Name (Name,liftSupply,PrimMap)
import Cryptol.ModuleSystem.Env (lookupModule
                                , LoadedModule(..)
                                , meCoreLint, CoreLint(..)
                                , ModulePath(..), modulePathLabel)
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
import Cryptol.Transform.AddModParams (addModParams)
import Cryptol.Utils.Ident (preludeName, interactiveName
                           , modNameChunks, notParamInstModName
                           , isParamInstModName )
import Cryptol.Utils.PP (pretty)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Logger(logPutStrLn, logPrint)

import Cryptol.Prelude (preludeContents)

import Cryptol.Transform.MonoValues (rewModule)

import qualified Control.Exception as X
import Control.Monad (unless,when)
import qualified Data.ByteString as B
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text.Encoding (decodeUtf8')
import System.Directory (doesFileExist, canonicalizePath)
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
import Prelude.Compat hiding ( (<>) )


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

parseModule :: ModulePath -> ModuleM (Fingerprint, P.Module PName)
parseModule path = do

  bytesRes <- case path of
                InFile p -> io (X.try (B.readFile p))
                InMem _ bs -> pure (Right bs)

  bytes <- case bytesRes of
    Right bytes -> return bytes
    Left exn ->
      case path of
        InFile p
          | IOE.isDoesNotExistError exn -> cantFindFile p
          | otherwise                   -> otherIOError p exn
        InMem p _ -> panic "parseModule"
                       [ "IOError for in-memory contetns???"
                       , "Label: " ++ show p
                       , "Exception: " ++ show exn ]

  txt <- case decodeUtf8' bytes of
    Right txt -> return txt
    Left e    -> badUtf8 path e

  let cfg = P.defaultConfig
              { P.cfgSource  = case path of
                                 InFile p -> p
                                 InMem l _ -> l
              , P.cfgPreProc = P.guessPreProc (modulePathLabel path)
              }

  case P.parseModule cfg txt of
    Right pm -> let fp = fingerprint bytes
                in fp `seq` return (fp, pm)
    Left err -> moduleParseError path err


-- Modules ---------------------------------------------------------------------

-- | Load a module by its path.
loadModuleByPath :: FilePath -> ModuleM T.Module
loadModuleByPath path = withPrependedSearchPath [ takeDirectory path ] $ do
  let fileName = takeFileName path
  foundPath <- findFile fileName
  (fp, pm) <- parseModule (InFile foundPath)
  let n = thing (P.mName pm)

  -- Check whether this module name has already been loaded from a different file
  env <- getModuleEnv
  -- path' is the resolved, absolute path, used only for checking
  -- whether it's already been loaded
  path' <- io (canonicalizePath foundPath)

  case lookupModule n env of
    -- loadModule will calculate the canonical path again
    Nothing -> doLoadModule (FromModule n) (InFile foundPath) fp pm
    Just lm
     | path' == loaded -> return (lmModule lm)
     | otherwise       -> duplicateModuleName n path' loaded
     where loaded = lmModuleId lm


-- | Load a module, unless it was previously loaded.
loadModuleFrom :: ImportSource -> ModuleM (ModulePath,T.Module)
loadModuleFrom isrc =
  do let n = importedModule isrc
     mb <- getLoadedMaybe n
     case mb of
       Just m -> return (lmFilePath m, lmModule m)
       Nothing ->
         do path <- findModule n
            errorInFile path $
              do (fp, pm) <- parseModule path
                 m        <- doLoadModule isrc path fp pm
                 return (path,m)

-- | Load dependencies, typecheck, and add to the eval environment.
doLoadModule ::
  ImportSource ->
  ModulePath ->
  Fingerprint ->
  P.Module PName ->
  ModuleM T.Module
doLoadModule isrc path fp pm0 =
  loading isrc $
  do let pm = addPrelude pm0
     loadDeps pm

     withLogger logPutStrLn
       ("Loading module " ++ pretty (P.thing (P.mName pm)))
     tcm <- optionalInstantiate =<< checkModule isrc path pm

     -- extend the eval env, unless a functor.
     unless (T.isParametrizedModule tcm) $ modifyEvalEnv (E.moduleEnv tcm)
     loadedModule path fp tcm

     return tcm
  where
  optionalInstantiate tcm
    | isParamInstModName (importedModule isrc) =
      if T.isParametrizedModule tcm then
        case addModParams tcm of
          Right tcm1 -> return tcm1
          Left xs    -> failedToParameterizeModDefs (T.mName tcm) xs
      else notAParameterizedModule (T.mName tcm)
    | otherwise = return tcm





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
moduleFile n = addExtension (joinPath (modNameChunks n))


-- | Discover a module.
findModule :: ModName -> ModuleM ModulePath
findModule n = do
  paths <- getSearchPath
  loop (possibleFiles paths)
  where
  loop paths = case paths of

    path:rest -> do
      b <- io (doesFileExist path)
      if b then return (InFile path) else loop rest

    [] -> handleNotFound

  handleNotFound =
    case n of
      m | m == preludeName -> pure (InMem "Cryptol" preludeContents)
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
loadDeps m =
  do mapM_ loadI (P.mImports m)
     mapM_ loadF (P.mInstance m)
  where
  loadI i = do (_,m1)  <- loadModuleFrom (FromImport i)
               when (T.isParametrizedModule m1) $ importParamModule $ T.mName m1
  loadF f = do _ <- loadModuleFrom (FromModuleInstance f)
               return ()



-- Type Checking ---------------------------------------------------------------

-- | Load the local environment, which consists of the environment for the
-- currently opened module, shadowed by the dynamic environment.
getLocalEnv :: ModuleM (IfaceParams,IfaceDecls,R.NamingEnv)
getLocalEnv  =
  do (params,decls,fNames,_) <- getFocusedEnv
     denv             <- getDynEnv
     let dynDecls = deIfaceDecls denv
     return (params,dynDecls `mappend` decls, deNames denv `R.shadowing` fNames)

-- | Typecheck a single expression, yielding a renamed parsed expression,
-- typechecked core expression, and a type schema.
checkExpr :: P.Expr PName -> ModuleM (P.Expr Name,T.Expr,T.Schema)
checkExpr e = do

  (params,decls,names) <- getLocalEnv

  -- run NoPat
  npe <- noPat e

  -- rename the expression with dynamic names shadowing the opened environment
  re  <- rename interactiveName names (R.rename npe)

  -- merge the dynamic and opened environments for typechecking
  prims <- getPrimMap
  let act  = TCAction { tcAction = T.tcExpr, tcLinter = exprLinter
                      , tcPrims = prims }
  (te,s) <- typecheck act re params decls

  return (re,te,s)

-- | Typecheck a group of declarations.
--
-- INVARIANT: This assumes that NoPat has already been run on the declarations.
checkDecls :: [P.TopDecl PName] -> ModuleM (R.NamingEnv,[T.DeclGroup])
checkDecls ds = do
  (params,decls,names) <- getLocalEnv

  -- introduce names for the declarations before renaming them
  declsEnv <- liftSupply (R.namingEnv' (map (R.InModule interactiveName) ds))
  rds <- rename interactiveName (declsEnv `R.shadowing` names)
             (traverse R.rename ds)

  prims <- getPrimMap
  let act  = TCAction { tcAction = T.tcDecls, tcLinter = declsLinter
                      , tcPrims = prims }
  ds' <- typecheck act rds params decls
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

-- | Load a module, be it a normal module or a functor instantiation.
checkModule :: ImportSource -> ModulePath -> P.Module PName -> ModuleM T.Module
checkModule isrc path m =
  case P.mInstance m of
    Nothing -> checkSingleModule T.tcModule isrc path m
    Just fmName -> do tf <- getLoaded (thing fmName)
                      checkSingleModule (T.tcModuleInst tf) isrc path m


-- | Typecheck a single module.  If the module is an instantiation
-- of a functor, then this just type-checks the instantiating parameters.
-- See 'checkModule'
checkSingleModule ::
  Act (P.Module Name) T.Module {- ^ how to check -} ->
  ImportSource                 {- ^ why are we loading this -} ->
  ModulePath                   {- path -} ->
  P.Module PName               {- ^ module to check -} ->
  ModuleM T.Module
checkSingleModule how isrc path m = do

  -- check that the name of the module matches expectations
  let nm = importedModule isrc
  unless (notParamInstModName nm == thing (P.mName m))
         (moduleNameMismatch nm (mName m))

  -- remove includes first; we only do this for actual files.
  -- it is less clear what should happen for in-memory things, and since
  -- this is a more-or-less obsolete feature, we are just not doing
  -- ot for now.
  e   <- case path of
           InFile p -> io (removeIncludesModule p m)
           InMem {} -> pure (Right m)

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
  let act = TCAction { tcAction = how
                     , tcLinter = moduleLinter (P.thing (P.mName m))
                     , tcPrims  = prims }


  tcm0 <- typecheck act scm noIfaceParams tcEnv

  let tcm = tcm0 -- fromMaybe tcm0 (addModParams tcm0)

  liftSupply (`rewModule` tcm)

data TCLinter o = TCLinter
  { lintCheck ::
      o -> T.InferInput -> Either TcSanity.Error [TcSanity.ProofObligation]
  , lintModule :: Maybe P.ModName
  }


exprLinter :: TCLinter (T.Expr, T.Schema)
exprLinter = TCLinter
  { lintCheck = \(e',s) i ->
      case TcSanity.tcExpr i e' of
        Left err     -> Left err
        Right (s1,os)
          | TcSanity.same s s1  -> Right os
          | otherwise -> Left (TcSanity.TypeMismatch "exprLinter" s s1)
  , lintModule = Nothing
  }

declsLinter :: TCLinter [ T.DeclGroup ]
declsLinter = TCLinter
  { lintCheck = \ds' i -> case TcSanity.tcDecls i ds' of
                            Left err -> Left err
                            Right os -> Right os

  , lintModule = Nothing
  }

moduleLinter :: P.ModName -> TCLinter T.Module
moduleLinter m = TCLinter
  { lintCheck   = \m' i -> case TcSanity.tcModule i m' of
                            Left err -> Left err
                            Right os -> Right os
  , lintModule  = Just m
  }

type Act i o = i -> T.InferInput -> IO (T.InferOutput o)

data TCAction i o = TCAction
  { tcAction :: Act i o
  , tcLinter :: TCLinter o
  , tcPrims  :: PrimMap
  }

typecheck ::
  (Show i, Show o, HasLoc i) => TCAction i o -> i ->
                                  IfaceParams -> IfaceDecls -> ModuleM o
typecheck act i params env = do

  let range = fromMaybe emptyRange (getLoc i)
  input <- genInferInput range (tcPrims act) params env
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
                           Right as ->
                             let ppIt l = mapM_ (logPrint l . T.pp)
                             in withLogger ppIt as
                           Left err -> panic "Core lint failed:" [show err]
         return o

    T.InferFailed warns errs ->
      do typeCheckWarnings warns
         typeCheckingFailed errs

-- | Generate input for the typechecker.
genInferInput :: Range -> PrimMap ->
                          IfaceParams -> IfaceDecls -> ModuleM T.InferInput
genInferInput r prims params env = do
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
    , T.inpAbstractTypes = ifAbstractTypes env
    , T.inpNameSeeds = seeds
    , T.inpMonoBinds = monoBinds
    , T.inpSolverConfig = cfg
    , T.inpSearchPath = searchPath
    , T.inpSupply    = supply
    , T.inpPrimNames = prims
    , T.inpParamTypes       = ifParamTypes params
    , T.inpParamConstraints = ifParamConstraints params
    , T.inpParamFuns        = ifParamFuns params
    }



-- Evaluation ------------------------------------------------------------------

evalExpr :: T.Expr -> ModuleM E.Value
evalExpr e = do
  env <- getEvalEnv
  denv <- getDynEnv
  evopts <- getEvalOpts
  io $ E.runEval evopts $ (E.evalExpr (env <> deEnv denv) e)

evalDecls :: [T.DeclGroup] -> ModuleM ()
evalDecls dgs = do
  env <- getEvalEnv
  denv <- getDynEnv
  evOpts <- getEvalOpts
  let env' = env <> deEnv denv
  deEnv' <- io $ E.runEval evOpts $ E.evalDecls dgs env'
  let denv' = denv { deDecls = deDecls denv ++ dgs
                   , deEnv = deEnv'
                   }
  setDynEnv denv'

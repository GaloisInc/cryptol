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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Cryptol.ModuleSystem.Base where

import qualified Control.Exception as X
import Control.Monad (unless,forM)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text.Encoding (decodeUtf8')
import System.Directory (doesFileExist, canonicalizePath)
import System.FilePath ( addExtension
                       , isAbsolute
                       , joinPath
                       , (</>)
                       , normalise
                       , takeDirectory
                       , takeFileName
                       )
import qualified System.IO.Error as IOE
import qualified Data.Map as Map

import Prelude ()
import Prelude.Compat hiding ( (<>) )



import Cryptol.ModuleSystem.Env (DynamicEnv(..))
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Monad
import Cryptol.ModuleSystem.Name (Name,liftSupply,PrimMap,ModPath(..))
import Cryptol.ModuleSystem.Env (lookupModule
                                , LoadedModule(..)
                                , meCoreLint, CoreLint(..)
                                , ModContext(..)
                                , ModulePath(..), modulePathLabel)
import qualified Cryptol.Eval                 as E
import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.Eval.Concrete (Concrete(..))
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

import Cryptol.Utils.Ident ( preludeName, floatName, arrayName, suiteBName, primeECName
                           , preludeReferenceName, interactiveName, modNameChunks
                           , notParamInstModName, isParamInstModName )
import Cryptol.Utils.PP (pretty)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Logger(logPutStrLn, logPrint)

import Cryptol.Prelude ( preludeContents, floatContents, arrayContents
                       , suiteBContents, primeECContents, preludeReferenceContents )
import Cryptol.Transform.MonoValues (rewModule)


-- Renaming --------------------------------------------------------------------

rename :: ModName -> R.NamingEnv -> R.RenameM a -> ModuleM a
rename modName env m = do
  ifaces <- getIfaces
  (res,ws) <- liftSupply $ \ supply ->
    let info = R.RenamerInfo
                 { renSupply  = supply
                 , renContext = TopModule modName
                 , renEnv     = env
                 , renIfaces  = ifaces
                 }
    in
    case R.runRenamer info m of
      (Right (a,supply'),ws) -> ((Right a,ws),supply')
      (Left errs,ws)         -> ((Left errs,ws),supply)

  renamerWarnings ws
  case res of
    Right r   -> return r
    Left errs -> renamerErrors errs

-- | Rename a module in the context of its imported modules.
renameModule :: P.Module PName -> ModuleM R.RenamedModule
renameModule m = rename (thing (mName m)) mempty (R.renameModule m)


-- NoPat -----------------------------------------------------------------------

-- | Run the noPat pass.
noPat :: RemovePatterns a => a -> ModuleM a
noPat a = do
  let (a',errs) = removePatterns a
  unless (null errs) (noPatErrors errs)
  return a'


-- Parsing ---------------------------------------------------------------------

parseModule :: ModulePath -> ModuleM (Fingerprint, [P.Module PName])
parseModule path = do
  getBytes <- getByteReader

  bytesRes <- case path of
                InFile p -> io (X.try (getBytes p))
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
  (fp, pms) <- parseModule (InFile foundPath)
  last <$>
    forM pms \pm ->
    do let n = thing (P.mName pm)

       -- Check whether this module name has already been loaded from a
       -- different file
       env <- getModuleEnv
       -- path' is the resolved, absolute path, used only for checking
       -- whether it's already been loaded
       path' <- io (canonicalizePath foundPath)

       case lookupModule n env of
         -- loadModule will calculate the canonical path again
         Nothing -> doLoadModule False (FromModule n) (InFile foundPath) fp pm
         Just lm
          | path' == loaded -> return (lmModule lm)
          | otherwise       -> duplicateModuleName n path' loaded
          where loaded = lmModuleId lm


-- | Load a module, unless it was previously loaded.
loadModuleFrom ::
  Bool {- ^ quiet mode -} -> ImportSource -> ModuleM (ModulePath,T.Module)
loadModuleFrom quiet isrc =
  do let n = importedModule isrc
     mb <- getLoadedMaybe n
     case mb of
       Just m -> return (lmFilePath m, lmModule m)
       Nothing ->
         do path <- findModule n
            errorInFile path $
              do (fp, pms) <- parseModule path
                 ms        <- mapM (doLoadModule quiet isrc path fp) pms
                 return (path,last ms)

-- | Load dependencies, typecheck, and add to the eval environment.
doLoadModule ::
  Bool {- ^ quiet mode: true suppresses the "loading module" message -} ->
  ImportSource ->
  ModulePath ->
  Fingerprint ->
  P.Module PName ->
  ModuleM T.Module
doLoadModule quiet isrc path fp pm0 =
  loading isrc $
  do let pm = addPrelude pm0
     loadDeps pm

     unless quiet $ withLogger logPutStrLn
       ("Loading module " ++ pretty (P.thing (P.mName pm)))


     (nameEnv,tcmod) <- checkModule isrc path pm
     tcm <- optionalInstantiate tcmod

     -- extend the eval env, unless a functor.
     tbl <- Concrete.primTable <$> getEvalOptsAction
     let ?evalPrim = \i -> Right <$> Map.lookup i tbl
     callStacks <- getCallStacks
     let ?callStacks = callStacks
     unless (T.isParametrizedModule tcm)
       $ modifyEvalEnv (E.moduleEnv Concrete tcm)
     loadedModule path fp nameEnv tcm

     return tcm
  where
  optionalInstantiate tcm
    | isParamInstModName (importedModule isrc) =
      failedToParameterizeModDefs (T.mName tcm)
    | otherwise = return tcm





-- | Rewrite an import declaration to be of the form:
--
-- > import foo as foo [ [hiding] (a,b,c) ]
fullyQualified :: P.Import -> P.Import
fullyQualified i = i { iAs = Just (iModule i) }

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
        | m == floatName   -> pure (InMem "Float" floatContents)
        | m == arrayName   -> pure (InMem "Array" arrayContents)
        | m == suiteBName  -> pure (InMem "SuiteB" suiteBContents)
        | m == primeECName -> pure (InMem "PrimeEC" primeECContents)
        | m == preludeReferenceName -> pure (InMem "Cryptol::Reference" preludeReferenceContents)
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
      if b then return (normalise path') else loop rest
    [] -> cantFindFile path
  possibleFiles paths = map (</> path) paths

-- | Add the prelude to the import list if it's not already mentioned.
addPrelude :: P.Module PName -> P.Module PName
addPrelude m
  | preludeName == P.thing (P.mName m) = m
  | preludeName `elem` importedMods    = m
  | otherwise                          = m { mDef = newDef }
  where
  newDef =
    case mDef m of
      NormalModule ds -> NormalModule (P.DImport prel : ds)
      FunctorInstance f as ins -> FunctorInstance f as ins
      SignatureModule s -> SignatureModule s { sigImports = prel : sigImports s }

  importedMods  = map (P.iModule . P.thing) (P.mImports m)
  prel = P.Located
    { P.srcRange = emptyRange
    , P.thing    = P.Import
      { iModule    = P.ImpTop preludeName
      , iAs        = Nothing
      , iSpec      = Nothing
      }
    }

-- | Load the dependencies of a module into the environment.
loadDeps :: P.ModuleG mname name -> ModuleM ()
loadDeps m =
  case mDef m of
    NormalModule ds -> mapM_ depsOfDecl ds
    FunctorInstance f as _ ->
      do loadImpName FromModuleInstance f
         case as of
           DefaultInstArg a      -> loadImpName FromModuleInstance a
           DefaultInstAnonArg ds -> mapM_ depsOfDecl ds
           NamedInstArgs args -> mapM_ loadInstArg args
    SignatureModule s -> mapM_ loadImpD (sigImports s)
  where
  loadI i = do _ <- loadModuleFrom False i
               pure ()

  loadImpName src l =
    case thing l of
      ImpTop f -> loadI (src l { thing = f })
      _        -> pure ()

  loadImpD li = loadImpName (FromImport . new) (iModule <$> li)
    where new i = i { thing = (thing li) { iModule = thing i } }

  loadInstArg (ModuleInstanceArg _ f) = loadImpName FromModuleInstance f

  depsOfDecl d =
    case d of
      DImport li -> loadImpD li

      DModule TopLevel { tlValue = NestedModule nm } -> loadDeps nm

      DModParam mo -> loadImpName FromSigImport s
        where s = mpSignature mo

      _ -> pure ()





-- Type Checking ---------------------------------------------------------------

-- | Typecheck a single expression, yielding a renamed parsed expression,
-- typechecked core expression, and a type schema.
checkExpr :: P.Expr PName -> ModuleM (P.Expr Name,T.Expr,T.Schema)
checkExpr e = do

  fe <- getFocusedEnv
  let params = mctxParams fe
      decls  = mctxDecls fe
      names  = mctxNames fe

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
checkDecls :: [P.TopDecl PName] -> ModuleM (R.NamingEnv,[T.DeclGroup], Map.Map Name T.TySyn)
checkDecls ds = do
  fe <- getFocusedEnv
  let params = mctxParams fe
      decls  = mctxDecls  fe
      names  = mctxNames  fe

  (declsEnv,rds) <- rename interactiveName names
                  $ R.renameTopDecls interactiveName ds
  prims <- getPrimMap
  let act  = TCAction { tcAction = T.tcDecls, tcLinter = declsLinter
                      , tcPrims = prims }
  (ds',tyMap) <- typecheck act rds params decls
  return (declsEnv,ds',tyMap)

-- | Generate the primitive map. If the prelude is currently being loaded, this
-- should be generated directly from the naming environment given to the renamer
-- instead.
getPrimMap :: ModuleM PrimMap
getPrimMap  =
  do env <- getModuleEnv
     let mkPrims = ifacePrimMap . lmInterface
         mp `alsoPrimFrom` m =
           case lookupModule m env of
             Nothing -> mp
             Just lm -> mkPrims lm <> mp

     case lookupModule preludeName env of
       Just prel -> return $ mkPrims prel
                            `alsoPrimFrom` floatName
       Nothing -> panic "Cryptol.ModuleSystem.Base.getPrimMap"
                  [ "Unable to find the prelude" ]

-- | Load a module, be it a normal module or a functor instantiation.
checkModule ::
  ImportSource -> ModulePath -> P.Module PName ->
  ModuleM (R.NamingEnv, T.Module)
checkModule isrc path m = checkSingleModule T.tcModule isrc path m
{-
  case mDef m of
    NormalModule _ -> 
    FunctorInstanceAnon fmName _ ->
      do mbtf <- getLoadedMaybe (thing fmName)
         case mbtf of
           Just tf ->
             do renThis <- io $ newIORef (lmNamingEnv tf)
                let how = T.tcModuleInst renThis (lmModule tf)
                (_,m') <- checkSingleModule how isrc path m
                newEnv <- io $ readIORef renThis
                pure (newEnv,m')
           Nothing -> panic "checkModule"
                        [ "Functor of module instantiation not loaded" ]

    -- XXX: functor instance; this is for top-level functor instances
-}

-- | Typecheck a single module.  If the module is an instantiation
-- of a functor, then this just type-checks the instantiating parameters.
-- See 'checkModule'
checkSingleModule ::
  Act (P.Module Name) T.Module {- ^ how to check -} ->
  ImportSource                 {- ^ why are we loading this -} ->
  ModulePath                   {- path -} ->
  P.Module PName               {- ^ module to check -} ->
  ModuleM (R.NamingEnv,T.Module)
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
           InFile p -> do
             r <- getByteReader
             io (removeIncludesModule r p m)
           InMem {} -> pure (Right m)

  nim <- case e of
           Right nim  -> return nim
           Left ierrs -> noIncludeErrors ierrs

  -- remove pattern bindings
  npm <- noPat nim

  -- rename everything
  renMod <- renameModule npm

{-
  -- dump renamed
  when (thing (mName (R.rmModule renMod)) /= preludeName)
       do (io $ print (T.pp renMod))
          -- io $ exitSuccess
-}

  -- when generating the prim map for the typechecker, if we're checking the
  -- prelude, we have to generate the map from the renaming environment, as we
  -- don't have the interface yet.
  prims <- if thing (mName m) == preludeName
              then return (R.toPrimMap (R.rmDefines renMod))
              else getPrimMap

  -- typecheck
  let act = TCAction { tcAction = how
                     , tcLinter = moduleLinter (P.thing (P.mName m))
                     , tcPrims  = prims }


  tcm0 <- typecheck act (R.rmModule renMod) Nothing (R.rmImported renMod)

  let tcm = tcm0 -- fromMaybe tcm0 (addModParams tcm0)

  rewMod <- liftSupply (`rewModule` tcm)
  pure (R.rmInScope renMod,rewMod)

data TCLinter o = TCLinter
  { lintCheck ::
      o -> T.InferInput -> Either (Range, TcSanity.Error) [TcSanity.ProofObligation]
  , lintModule :: Maybe P.ModName
  }


exprLinter :: TCLinter (T.Expr, T.Schema)
exprLinter = TCLinter
  { lintCheck = \(e',s) i ->
      case TcSanity.tcExpr i e' of
        Left err     -> Left err
        Right (s1,os)
          | TcSanity.same s s1  -> Right os
          | otherwise -> Left ( fromMaybe emptyRange (getLoc e')
                              , TcSanity.TypeMismatch "exprLinter" s s1
                              )
  , lintModule = Nothing
  }

declsLinter :: TCLinter ([ T.DeclGroup ], a)
declsLinter = TCLinter
  { lintCheck = \(ds',_) i -> case TcSanity.tcDecls i ds' of
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
  (Show i, Show o, HasLoc i) =>
  TCAction i o -> i -> Maybe IfaceFunctorParams -> IfaceDecls -> ModuleM o
typecheck act i params env = do

  let range = fromMaybe emptyRange (getLoc i)
  input <- genInferInput range (tcPrims act) params env
  out   <- io (tcAction act i input)

  case out of

    T.InferOK nameMap warns seeds supply' o ->
      do setNameSeeds seeds
         setSupply supply'
         typeCheckWarnings nameMap warns
         menv <- getModuleEnv
         case meCoreLint menv of
           NoCoreLint -> return ()
           CoreLint   -> case lintCheck (tcLinter act) o input of
                           Right as ->
                             let ppIt l = mapM_ (logPrint l . T.pp)
                             in withLogger ppIt as
                           Left err -> panic "Core lint failed:" [show err]
         return o

    T.InferFailed nameMap warns errs ->
      do typeCheckWarnings nameMap warns
         typeCheckingFailed nameMap errs

-- | Generate input for the typechecker.
genInferInput ::
  Range -> PrimMap -> Maybe IfaceFunctorParams -> IfaceDecls ->
  ModuleM T.InferInput
genInferInput r prims mbParams env' = do
  seeds <- getNameSeeds
  monoBinds <- getMonoBinds
  solver <- getTCSolver
  supply <- getSupply
  searchPath <- getSearchPath
  callStacks <- getCallStacks

  -- TODO: include the environment needed by the module
  let env = env'
            -- XXX: we should really just pass this directly

      (paramTys,paramCtrs,paramVs) =
        case mbParams of
          Nothing -> (mempty,mempty,mempty)
          Just (OldStyle p) ->
            (ifParamTypes p, ifParamConstraints p, ifParamFuns p)
          Just (NewStyle p) ->
            let ps = map ifmpParameters (Map.elems p)
            in ( mconcat (map ifParamTypes ps)
               , mconcat (map ifParamConstraints ps)
               , mconcat (map ifParamFuns ps)
               )

  topMods <- getAllLoaded

  return T.InferInput
    { T.inpRange     = r
    , T.inpVars      = Map.map ifDeclSig (ifDecls env)
    , T.inpTSyns     = ifTySyns env
    , T.inpNewtypes  = ifNewtypes env
    , T.inpAbstractTypes = ifAbstractTypes env
    , T.inpSignatures = ifSignatures env
    , T.inpNameSeeds = seeds
    , T.inpMonoBinds = monoBinds
    , T.inpCallStacks = callStacks
    , T.inpSearchPath = searchPath
    , T.inpSupply    = supply
    , T.inpPrimNames = prims
    , T.inpParamTypes       = paramTys
    , T.inpParamConstraints = paramCtrs
    , T.inpParamFuns        = paramVs
    , T.inpSolver           = solver
    , T.inpTopModules = topMods
    }


-- Evaluation ------------------------------------------------------------------

evalExpr :: T.Expr -> ModuleM Concrete.Value
evalExpr e = do
  env <- getEvalEnv
  denv <- getDynEnv
  evopts <- getEvalOptsAction
  let tbl = Concrete.primTable evopts
  let ?evalPrim = \i -> Right <$> Map.lookup i tbl
  let ?range = emptyRange
  callStacks <- getCallStacks
  let ?callStacks = callStacks

  io $ E.runEval mempty (E.evalExpr Concrete (env <> deEnv denv) e)

evalDecls :: [T.DeclGroup] -> ModuleM ()
evalDecls dgs = do
  env <- getEvalEnv
  denv <- getDynEnv
  evOpts <- getEvalOptsAction
  let env' = env <> deEnv denv
  let tbl = Concrete.primTable evOpts
  let ?evalPrim = \i -> Right <$> Map.lookup i tbl
  callStacks <- getCallStacks
  let ?callStacks = callStacks

  deEnv' <- io $ E.runEval mempty (E.evalDecls Concrete dgs env')
  let denv' = denv { deDecls = deDecls denv ++ dgs
                   , deEnv = deEnv'
                   }
  setDynEnv denv'

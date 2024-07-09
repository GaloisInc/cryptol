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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

module Cryptol.ModuleSystem.Base where

import qualified Control.Exception as X
import Control.Monad (unless,forM)
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.List(sortBy)
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import Data.Function(on)
import Data.Monoid ((<>),Endo(..), Any(..))
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



import Cryptol.ModuleSystem.Fingerprint
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Monad
import Cryptol.ModuleSystem.Name (Name,liftSupply,PrimMap,ModPath(..),nameIdent)
import Cryptol.ModuleSystem.Env ( DynamicEnv(..),FileInfo(..),fileInfo
                                , lookupModule
                                , lookupTCEntity
                                , LoadedModuleG(..), lmInterface
                                , meCoreLint, CoreLint(..)
                                , ModContext(..), ModContextParams(..)
                                , ModulePath(..), modulePathLabel
                                , EvalForeignPolicy (..))
import           Cryptol.Backend.FFI
import qualified Cryptol.Eval                 as E
import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.Eval.Concrete (Concrete(..))
import           Cryptol.Eval.FFI
import qualified Cryptol.ModuleSystem.NamingEnv as R
import qualified Cryptol.ModuleSystem.Renamer as R
import qualified Cryptol.Parser               as P
import qualified Cryptol.Parser.Unlit         as P
import Cryptol.Parser.AST as P
import Cryptol.Parser.NoPat (RemovePatterns(removePatterns))
import qualified Cryptol.Parser.ExpandPropGuards as ExpandPropGuards
  ( expandPropGuards, runExpandPropGuardsM )
import Cryptol.Parser.NoInclude (removeIncludesModule)
import Cryptol.Parser.Position (HasLoc(..), Range, emptyRange)
import qualified Cryptol.TypeCheck     as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.PP as T
import qualified Cryptol.TypeCheck.Sanity as TcSanity
import qualified Cryptol.Backend.FFI.Error as FFI

import Cryptol.Utils.Ident ( preludeName, floatName, arrayName, suiteBName, primeECName
                           , preludeReferenceName, interactiveName, modNameChunks
                           , modNameToNormalModName, Namespace(NSModule) )
import Cryptol.Utils.PP (pretty, pp, hang, vcat, ($$), (<+>), (<.>), colon)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Logger(logPutStrLn, logPrint)
import Cryptol.Utils.Benchmark

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

renameImpNameInCurrentEnv :: P.ImpName PName -> ModuleM (P.ImpName Name)
renameImpNameInCurrentEnv (P.ImpTop top) =
 do ok <- isLoaded top
    if ok then
      pure (P.ImpTop top)
    else
      fail ("Top-level module not loaded: " ++ show (pp top))
renameImpNameInCurrentEnv (P.ImpNested pname) =
 do env <- getFocusedEnv
    case R.lookupListNS NSModule pname (mctxNames env) of
      [] -> do
        fail ("Undefined submodule name: " ++ show (pp pname))
      _:_:_ -> do
        fail ("Ambiguous submodule name: " ++ show (pp pname))
      [name] -> pure (P.ImpNested name)

-- NoPat -----------------------------------------------------------------------

-- | Run the noPat pass.
noPat :: RemovePatterns a => a -> ModuleM a
noPat a = do
  let (a',errs) = removePatterns a
  unless (null errs) (noPatErrors errs)
  return a'

-- ExpandPropGuards ------------------------------------------------------------

-- | Run the expandPropGuards pass.
expandPropGuards :: Module PName -> ModuleM (Module PName)
expandPropGuards a =
  case ExpandPropGuards.runExpandPropGuardsM $ ExpandPropGuards.expandPropGuards a of
    Left err -> expandPropGuardsError err
    Right a' -> pure a'

-- Parsing ---------------------------------------------------------------------

-- | Parse a module and expand includes
-- Returns a fingerprint of the module, and a set of dependencies due
-- to `include` directives.
parseModule ::
  ModulePath -> ModuleM (Fingerprint, Set FilePath, [P.Module PName])
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
    Right pms ->
      do let fp = fingerprint bytes
         (pm1,deps) <-
           case path of
             InFile p ->
               do r <- getByteReader
                  (mo,d) <- unzip <$>
                    forM pms \pm ->
                    do mb <- io (removeIncludesModule r p pm)
                       case mb of
                         Right ok -> pure ok
                         Left err -> noIncludeErrors err
                  pure (mo, Set.unions d)

             {- We don't do "include" resolution for in-memory files
                because at the moment the include resolution pass requires
                the path to the file to be known---this is used when
                looking for other inlcude files.  This could be
                generalized, but we can do it once we have a concrete use
                case as it would help guide the design. -}
             InMem {} -> pure (pms, Set.empty)

{-
         case path of
           InFile {} -> io $ print (T.vcat (map T.pp pm1))
           InMem {} -> pure ()
--}
         fp `seq` return (fp, deps, pm1)

    Left err -> moduleParseError path err


-- Top Level Modules and Signatures --------------------------------------------


-- | Load a module by its path.
loadModuleByPath ::
  Bool {- ^ evaluate declarations in the module -} ->
  FilePath -> ModuleM T.TCTopEntity
loadModuleByPath eval path = withPrependedSearchPath [ takeDirectory path ] $ do
  let fileName = takeFileName path
  foundPath <- findFile fileName
  (fp, deps, pms) <- parseModule (InFile foundPath)
  last <$>
    forM pms \pm ->
    do let n = thing (P.mName pm)

       -- Check whether this module name has already been loaded from a
       -- different file
       env <- getModuleEnv
       -- path' is the resolved, absolute path, used only for checking
       -- whether it's already been loaded
       path' <- io (canonicalizePath foundPath)

       case lookupTCEntity n env of
         -- loadModule will calculate the canonical path again
         Nothing ->
           doLoadModule eval False (FromModule n) (InFile foundPath) fp deps pm
         Just lm
          | path' == loaded -> return (lmData lm)
          | otherwise       -> duplicateModuleName n path' loaded
          where loaded = lmModuleId lm


-- | Load a module, unless it was previously loaded.
loadModuleFrom ::
  Bool {- ^ quiet mode -} -> ImportSource -> ModuleM (ModulePath,T.TCTopEntity)
loadModuleFrom quiet isrc =
  do let n = importedModule isrc
     mb <- getLoadedMaybe n
     case mb of
       Just m -> return (lmFilePath m, lmData m)
       Nothing ->
         do path <- findModule n
            errorInFile path $
              do (fp, deps, pms) <- parseModule path
                 ms <- mapM (doLoadModule True quiet isrc path fp deps) pms
                 return (path,last ms)

-- | Load dependencies, typecheck, and add to the eval environment.
doLoadModule ::
  Bool {- ^ evaluate declarations in the module -} ->
  Bool {- ^ quiet mode: true suppresses the "loading module" message -} ->
  ImportSource ->
  ModulePath ->
  Fingerprint ->
  Set FilePath {- ^ `include` dependencies -} ->
  P.Module PName ->
  ModuleM T.TCTopEntity
doLoadModule eval quiet isrc path fp incDeps pm0 =
  loading isrc $
  do let pm = addPrelude pm0
     impDeps <- loadDeps pm

     let what = case P.mDef pm of
                  P.InterfaceModule {} -> "interface module"
                  _                    -> "module"

     unless quiet $ withLogger logPutStrLn
       ("Loading " ++ what ++ " " ++ pretty (P.thing (P.mName pm)))


     (nameEnv,tcm) <- checkModule isrc pm

     -- extend the eval env, unless a functor.
     tbl <- Concrete.primTable <$> getEvalOptsAction
     let ?evalPrim = \i -> Right <$> Map.lookup i tbl
     callStacks <- getCallStacks
     let ?callStacks = callStacks
     let shouldEval =
           case tcm of
             T.TCTopModule m | eval && not (T.isParametrizedModule m) -> Just m
             _ -> Nothing

     foreignSrc <- case shouldEval of
                      Just m ->
                        do fsrc <- evalForeign m
                           modifyEvalEnv (E.moduleEnv Concrete m)
                           pure fsrc
                      Nothing -> pure Nothing

     let fi = fileInfo fp incDeps impDeps foreignSrc
     loadedModule path fi nameEnv foreignSrc tcm

     return tcm

  where
  evalForeign tcm
    | not (null foreignFs) =
      ffiLoadErrors (T.mName tcm) (map FFI.FFIInFunctor foreignFs)
    | not (null dups) =
      ffiLoadErrors (T.mName tcm) (map FFI.FFIDuplicates dups)
    | null foreigns = pure Nothing
    | otherwise =
      getEvalForeignPolicy >>= \case
        AlwaysEvalForeign -> doEvalForeign (ffiLoadErrors (T.mName tcm))
        PreferEvalForeign -> doEvalForeign \errs ->
          withLogger logPrint $
            hang
              ("[warning] Could not load all foreign implementations for module"
                <+> pp (T.mName tcm) <.> colon) 4 $
              vcat (map pp errs)
              $$ "Fallback cryptol implementations will be used if available"
        NeverEvalForeign -> pure Nothing

    where foreigns  = findForeignDecls tcm
          foreignFs = T.findForeignDeclsInFunctors tcm
          dups      = [ d | d@(_ :| _ : _) <- NE.groupBy ((==) `on` nameIdent)
                                            $ sortBy (compare `on` nameIdent)
                                            $ map fst foreigns ]
          doEvalForeign handleErrs =
            case path of
              InFile p -> io (loadForeignSrc p) >>=
                \case

                  Right fsrc -> do
                    unless quiet $
                      case getForeignSrcPath fsrc of
                        Just fpath -> withLogger logPutStrLn $
                          "Loading dynamic library " ++ takeFileName fpath
                        Nothing -> pure ()
                    (errs, ()) <-
                      modifyEvalEnvM (evalForeignDecls fsrc foreigns)
                    unless (null errs) $
                      handleErrs errs
                    pure $ Just fsrc

                  Left err -> do
                    handleErrs [err]
                    pure Nothing

              InMem m _ -> panic "doLoadModule"
                ["Can't find foreign source of in-memory module", m]

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
findFile path
  | isAbsolute path =
    do -- No search path checking for absolute paths
       b <- io (doesFileExist path)
       if b then return path else cantFindFile path
  | otherwise =
    do paths <- getSearchPath
       loop (possibleFiles paths)
       where
       loop paths = case paths of
                      path' : rest ->
                        do b <- io (doesFileExist path')
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
      InterfaceModule s -> InterfaceModule s { sigImports = prel
                                             : sigImports s }

  importedMods  = map (P.iModule . P.thing) (P.mImports m)
  prel = P.Located
    { P.srcRange = emptyRange
    , P.thing    = P.Import
      { iModule  = P.ImpTop preludeName
      , iAs      = Nothing
      , iSpec    = Nothing
      , iInst    = Nothing
      , iDoc     = Nothing
      }
    }

-- | Load the dependencies of a module into the environment.
loadDeps :: P.ModuleG mname name -> ModuleM (Set ModName)
loadDeps m =
  do let ds = findDeps m
     mapM_ (loadModuleFrom False) ds
     pure (Set.fromList (map importedModule ds))

-- | Find all imports in a module.
findDeps :: P.ModuleG mname name -> [ImportSource]
findDeps m = appEndo (snd (findDeps' m)) []

findDepsOfModule :: ModName -> ModuleM (ModulePath, FileInfo)
findDepsOfModule m =
  do mpath <- findModule m
     findDepsOf mpath

findDepsOf :: ModulePath -> ModuleM (ModulePath, FileInfo)
findDepsOf mpath =
  do (fp, incs, ms) <- parseModule mpath
     let (anyF,imps) = mconcat (map (findDeps' . addPrelude) ms)
     fdeps <- if getAny anyF
                then do mb <- io case mpath of
                                   InFile path -> foreignLibPath path
                                   InMem {}    -> pure Nothing
                        pure case mb of
                               Nothing -> Map.empty
                               Just (fpath, exists) ->
                                 Map.singleton fpath exists
                else pure Map.empty
     pure
       ( mpath
       , FileInfo
           { fiFingerprint = fp
           , fiIncludeDeps = incs
           , fiImportDeps  = Set.fromList (map importedModule (appEndo imps []))
           , fiForeignDeps = fdeps
           }
       )

-- | Find the set of top-level modules imported by a module.
findModuleDeps :: P.ModuleG mname name -> Set P.ModName
findModuleDeps = Set.fromList . map importedModule . findDeps

-- | A helper `findDeps` and `findModuleDeps` that actually does the searching.
findDeps' :: P.ModuleG mname name -> (Any, Endo [ImportSource])
findDeps' m =
  case mDef m of
    NormalModule ds -> mconcat (map depsOfDecl ds)
    FunctorInstance f as _ ->
      let fds = loadImpName FromModuleInstance f
          ads = case as of
                  DefaultInstArg a -> loadInstArg a
                  DefaultInstAnonArg ds -> mconcat (map depsOfDecl ds)
                  NamedInstArgs args -> mconcat (map loadNamedInstArg args)
      in fds <> ads
    InterfaceModule s -> mconcat (map loadImpD (sigImports s))
  where
  loadI i = (mempty, Endo (i:))

  loadImpName src l =
    case thing l of
      ImpTop f -> loadI (src l { thing = f })
      _        -> mempty

  loadImpD li = loadImpName (FromImport . new) (iModule <$> li)
    where new i = i { thing = (thing li) { iModule = thing i } }

  loadNamedInstArg (ModuleInstanceNamedArg _ f) = loadInstArg f
  loadInstArg f =
    case thing f of
      ModuleArg mo -> loadImpName FromModuleInstance f { thing = mo }
      _            -> mempty

  depsOfDecl d =
    case d of
      DImport li -> loadImpD li

      DModule TopLevel { tlValue = NestedModule nm } -> findDeps' nm

      DModParam mo -> loadImpName FromSigImport s
        where s = mpSignature mo

      Decl dd -> depsOfDecl' (tlValue dd)

      _ -> mempty

  depsOfDecl' d =
    case d of
      DLocated d' _ -> depsOfDecl' d'
      DBind b ->
        case thing (bDef b) of
          DForeign {} -> (Any True, mempty)
          _ -> mempty
      _ -> mempty






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

-- | Typecheck a single module.
-- Note: we assume that @include@s have already been processed
checkModule ::
  ImportSource                      {- ^ why are we loading this -} ->
  P.Module PName                    {- ^ module to check -} ->
  ModuleM (R.NamingEnv,T.TCTopEntity)
checkModule isrc m = do

  -- check that the name of the module matches expectations
  let nm = importedModule isrc
  unless (modNameToNormalModName nm ==
                                  modNameToNormalModName (thing (P.mName m)))
         (moduleNameMismatch nm (mName m))

  -- remove pattern bindings
  npm <- noPat m

  -- run expandPropGuards
  epgm <- expandPropGuards npm

  -- rename everything
  renMod <- renameModule epgm


  {- dump renamed
  unless (thing (mName (R.rmModule renMod)) == preludeName)
       do (io $ print (T.pp renMod))
          -- io $ exitSuccess
  --}


  -- when generating the prim map for the typechecker, if we're checking the
  -- prelude, we have to generate the map from the renaming environment, as we
  -- don't have the interface yet.
  prims <- if thing (mName m) == preludeName
              then return (R.toPrimMap (R.rmDefines renMod))
              else getPrimMap

  -- typecheck
  let act = TCAction { tcAction = T.tcModule
                     , tcLinter = tcTopEntitytLinter (P.thing (P.mName m))
                     , tcPrims  = prims }


  tcm <- typecheck act (R.rmModule renMod) NoParams (R.rmImported renMod)

  rewMod <- case tcm of
              T.TCTopModule mo -> T.TCTopModule <$> liftSupply (`rewModule` mo)
              T.TCTopSignature {} -> pure tcm
  let nameEnv = case tcm of
                  T.TCTopModule mo -> T.mInScope mo
                  -- Name env for signatures does not change after typechecking
                  T.TCTopSignature {} -> mInScope (R.rmModule renMod)
  pure (nameEnv,rewMod)

data TCLinter o = TCLinter
  { lintCheck ::
      o -> T.InferInput ->
                    Either (Range, TcSanity.Error) [TcSanity.ProofObligation]
  , lintModule :: Maybe P.ModName
  }


exprLinter :: TCLinter (T.Expr, T.Schema)
exprLinter = TCLinter
  { lintCheck = \(e',s) i ->
      case TcSanity.tcExpr i e' of
        Left err     -> Left err
        Right (s1,os)
          | TcSanity.SameIf os' <- TcSanity.same s s1 ->
                                        Right (map T.tMono os' ++ os)
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

tcTopEntitytLinter :: P.ModName -> TCLinter T.TCTopEntity
tcTopEntitytLinter m = TCLinter
  { lintCheck   = \m' i -> case m' of
                             T.TCTopModule mo ->
                               lintCheck (moduleLinter m) mo i
                             T.TCTopSignature {} -> Right []
                                -- XXX: what can we lint about module interfaces
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
  TCAction i o -> i -> ModContextParams -> IfaceDecls -> ModuleM o
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
                             in withLogger ppIt (TcSanity.onlyNonTrivial as)
                           Left (loc,err) ->
                            panic "Core lint failed:"
                              [ "Location: " ++ show (T.pp loc)
                              , show (T.pp err)
                              ]
         return o

    T.InferFailed nameMap warns errs ->
      do typeCheckWarnings nameMap warns
         typeCheckingFailed nameMap errs

-- | Generate input for the typechecker.
genInferInput :: Range -> PrimMap -> ModContextParams -> IfaceDecls ->
                                                          ModuleM T.InferInput
genInferInput r prims params env = do
  seeds <- getNameSeeds
  monoBinds <- getMonoBinds
  solver <- getTCSolver
  supply <- getSupply
  searchPath <- getSearchPath
  callStacks <- getCallStacks

  topMods <- getAllLoaded
  topSigs <- getAllLoadedSignatures

  return T.InferInput
    { T.inpRange            = r
    , T.inpVars             = Map.map ifDeclSig (ifDecls env)
    , T.inpTSyns            = ifTySyns env
    , T.inpNominalTypes     = ifNominalTypes env
    , T.inpSignatures       = ifSignatures env
    , T.inpNameSeeds        = seeds
    , T.inpMonoBinds        = monoBinds
    , T.inpCallStacks       = callStacks
    , T.inpSearchPath       = searchPath
    , T.inpSupply           = supply
    , T.inpParams           = case params of
                                NoParams -> T.allParamNames mempty
                                FunctorParams ps -> T.allParamNames ps
                                InterfaceParams ps -> ps
    , T.inpPrimNames        = prims
    , T.inpSolver           = solver
    , T.inpTopModules       = topMods
    , T.inpTopSignatures    = topSigs
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

benchmarkExpr :: Double -> T.Expr -> ModuleM BenchmarkStats
benchmarkExpr period e = do
  env <- getEvalEnv
  denv <- getDynEnv
  evopts <- getEvalOptsAction
  let env' = env <> deEnv denv
  let tbl = Concrete.primTable evopts
  let ?evalPrim = \i -> Right <$> Map.lookup i tbl
  let ?range = emptyRange
  callStacks <- getCallStacks
  let ?callStacks = callStacks

  let eval expr = E.runEval mempty $
        E.evalExpr Concrete env' expr >>= E.forceValue
  io $ benchmark period eval e

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

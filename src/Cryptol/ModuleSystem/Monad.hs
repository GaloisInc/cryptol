-- |
-- Module      :  Cryptol.ModuleSystem.Monad
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
module Cryptol.ModuleSystem.Monad where

import           Cryptol.Eval (EvalEnv,EvalOpts(..))

import           Cryptol.Eval.FFI.ForeignSrc (ForeignSrc)
import           Cryptol.Eval.FFI.Error
import qualified Cryptol.Backend.Monad           as E

import           Cryptol.ModuleSystem.Env
import qualified Cryptol.ModuleSystem.Env as MEnv
import           Cryptol.ModuleSystem.Interface
import           Cryptol.ModuleSystem.Name (FreshM(..),Supply)
import           Cryptol.ModuleSystem.Renamer (RenamerError(),RenamerWarning())
import           Cryptol.ModuleSystem.NamingEnv(NamingEnv)
import           Cryptol.ModuleSystem.Fingerprint(Fingerprint)
import qualified Cryptol.Parser     as Parser
import qualified Cryptol.Parser.AST as P
import           Cryptol.Utils.Panic (panic)
import qualified Cryptol.Parser.NoPat as NoPat
import qualified Cryptol.Parser.ExpandPropGuards as ExpandPropGuards
import qualified Cryptol.Parser.NoInclude as NoInc
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Solver.SMT as SMT

import           Cryptol.Parser.Position (Range, Located)
import           Cryptol.Utils.Ident (interactiveName, noModuleName)
import           Cryptol.Utils.PP
import           Cryptol.Utils.Logger(Logger)
import qualified Cryptol.Project.Config as Proj

import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class
import Control.Exception (IOException)
import Data.ByteString (ByteString)
import Data.Function (on)
import Data.Functor.Identity
import Data.Map (Map)
import Data.Text.Encoding.Error (UnicodeException)
import Data.Traversable
import MonadLib
import System.Directory (canonicalizePath)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat


-- Errors ----------------------------------------------------------------------

data ImportSource
  = FromModule P.ModName
  | FromImport (Located P.Import)
  | FromSigImport (Located P.ModName)
  | FromModuleInstance (Located P.ModName)
    deriving (Show, Generic, NFData)

instance Eq ImportSource where
  (==) = (==) `on` importedModule

instance PP ImportSource where
  ppPrec _ is = case is of
    FromModule n  -> text "module name" <+> pp n
    FromImport li -> text "import of module" <+> pp (P.iModule (P.thing li))
    FromSigImport l -> text "import of interface" <+> pp (P.thing l)
    FromModuleInstance l ->
      text "instantiation of module" <+> pp (P.thing l)

importedModule :: ImportSource -> P.ModName
importedModule is =
  case is of
    FromModule n          -> n
    FromImport li         -> P.iModule (P.thing li)
    FromModuleInstance l  -> P.thing l
    FromSigImport l       -> P.thing l


data ModuleError
  = ModuleNotFound P.ModName [FilePath]
    -- ^ Unable to find the module given, tried looking in these paths
  | CantFindFile FilePath
    -- ^ Unable to open a file
  | BadUtf8 ModulePath Fingerprint UnicodeException
    -- ^ Bad UTF-8 encoding in while decoding this file
  | OtherIOError FilePath IOException
    -- ^ Some other IO error occurred while reading this file
  | ModuleParseError ModulePath Fingerprint Parser.ParseError
    -- ^ Generated this parse error when parsing the file for module m
  | RecursiveModules [ImportSource]
    -- ^ Recursive module group discovered
  | RenamerErrors ImportSource [RenamerError]
    -- ^ Problems during the renaming phase
  | NoPatErrors ImportSource [NoPat.Error]
    -- ^ Problems during the NoPat phase
  | ExpandPropGuardsError ImportSource ExpandPropGuards.Error
    -- ^ Problems during the ExpandPropGuards phase
  | NoIncludeErrors ImportSource [NoInc.IncludeError]
    -- ^ Problems during the NoInclude phase
  | TypeCheckingFailed ImportSource T.NameMap [(Range,T.Error)]
    -- ^ Problems during type checking
  | OtherFailure String
    -- ^ Problems after type checking, eg. specialization
  | ModuleNameMismatch P.ModName (Located P.ModName)
    -- ^ Module loaded by 'import' statement has the wrong module name
  | DuplicateModuleName P.ModName FilePath FilePath
    -- ^ Two modules loaded from different files have the same module name
  | FFILoadErrors P.ModName [FFILoadError]
    -- ^ Errors loading foreign function implementations
  | ConfigLoadError Proj.ConfigLoadError
  | ErrorInFile ModulePath ModuleError
    -- ^ This is just a tag on the error, indicating the file containing it.
    -- It is convenient when we had to look for the module, and we'd like
    -- to communicate the location of the problematic module to the handler.

    deriving (Show)

instance NFData ModuleError where
  rnf e = case e of
    ModuleNotFound src path              -> src `deepseq` path `deepseq` ()
    CantFindFile path                    -> path `deepseq` ()
    BadUtf8 path fp ue                   -> rnf (path, fp, ue)
    OtherIOError path exn                -> path `deepseq` exn `seq` ()
    ModuleParseError source fp err       -> rnf (source, fp, err)
    RecursiveModules mods                -> mods `deepseq` ()
    RenamerErrors src errs               -> src `deepseq` errs `deepseq` ()
    NoPatErrors src errs                 -> src `deepseq` errs `deepseq` ()
    ExpandPropGuardsError src err        -> src `deepseq` err `deepseq` ()
    NoIncludeErrors src errs             -> src `deepseq` errs `deepseq` ()
    TypeCheckingFailed nm src errs       -> nm `deepseq` src `deepseq` errs `deepseq` ()
    ModuleNameMismatch expected found    ->
      expected `deepseq` found `deepseq` ()
    DuplicateModuleName name path1 path2 ->
      name `deepseq` path1 `deepseq` path2 `deepseq` ()
    OtherFailure x                       -> x `deepseq` ()
    FFILoadErrors x errs                 -> x `deepseq` errs `deepseq` ()
    ErrorInFile x y                      -> x `deepseq` y `deepseq` ()
    ConfigLoadError x                    -> x `seq` ()

instance PP ModuleError where
  ppPrec prec e = case e of

    ModuleNotFound src path ->
      text "[error]" <+>
      text "Could not find module" <+> pp src
      $$
      hang (text "Searched paths:")
         4 (vcat (map text path))
      $$
      text "Set the CRYPTOLPATH environment variable to search more directories"

    CantFindFile path ->
      text "[error]" <+>
      text "can't find file:" <+> text path

    BadUtf8 path _fp _ue ->
      text "[error]" <+>
      text "bad utf-8 encoding:" <+> pp path

    OtherIOError path exn ->
      hang (text "[error]" <+>
            text "IO error while loading file:" <+> text path <.> colon)
         4 (text (show exn))

    ModuleParseError _source _fp err -> Parser.ppError err

    RecursiveModules mods ->
      hang (text "[error] module imports form a cycle:")
         4 (vcat (map pp (reverse mods)))

    RenamerErrors _src errs -> vcat (map pp errs)

    NoPatErrors _src errs -> vcat (map pp errs)

    ExpandPropGuardsError _src err -> pp err

    NoIncludeErrors _src errs -> vcat (map NoInc.ppIncludeError errs)

    TypeCheckingFailed _src nm errs -> vcat (map (T.ppNamedError nm) errs)

    ModuleNameMismatch expected found ->
      hang (text "[error]" <+> pp (P.srcRange found) <.> char ':')
         4 (vcat [ text "File name does not match module name:"
                 , text "  Actual:" <+> pp (P.thing found)
                 , text "Expected:" <+> pp expected
                 ])

    DuplicateModuleName name path1 path2 ->
      hang (text "[error] module" <+> pp name <+>
            text "is defined in multiple files:")
         4 (vcat [text path1, text path2])

    OtherFailure x -> text x

    FFILoadErrors x errs ->
      hang (text "[error] Failed to load foreign implementations for module"
            <+> pp x <.> colon)
         4 (vcat $ map pp errs)
      
    ConfigLoadError err -> pp err

    ErrorInFile _ x -> ppPrec prec x

moduleNotFound :: P.ModName -> [FilePath] -> ModuleM a
moduleNotFound name paths = ModuleT (raise (ModuleNotFound name paths))

cantFindFile :: FilePath -> ModuleM a
cantFindFile path = ModuleT (raise (CantFindFile path))

badUtf8 :: ModulePath -> Fingerprint -> UnicodeException -> ModuleM a
badUtf8 path fp ue = ModuleT (raise (BadUtf8 path fp ue))

otherIOError :: FilePath -> IOException -> ModuleM a
otherIOError path exn = ModuleT (raise (OtherIOError path exn))

moduleParseError :: ModulePath -> Fingerprint -> Parser.ParseError -> ModuleM a
moduleParseError path fp err =
  ModuleT (raise (ModuleParseError path fp err))

recursiveModules :: [ImportSource] -> ModuleM a
recursiveModules loaded = ModuleT (raise (RecursiveModules loaded))

renamerErrors :: [RenamerError] -> ModuleM a
renamerErrors errs = do
  src <- getImportSource
  ModuleT (raise (RenamerErrors src errs))

noPatErrors :: [NoPat.Error] -> ModuleM a
noPatErrors errs = do
  src <- getImportSource
  ModuleT (raise (NoPatErrors src errs))

expandPropGuardsError :: ExpandPropGuards.Error -> ModuleM a
expandPropGuardsError err = do
  src <- getImportSource
  ModuleT (raise (ExpandPropGuardsError src err))

noIncludeErrors :: [NoInc.IncludeError] -> ModuleM a
noIncludeErrors errs = do
  src <- getImportSource
  ModuleT (raise (NoIncludeErrors src errs))

typeCheckingFailed :: T.NameMap -> [(Range,T.Error)] -> ModuleM a
typeCheckingFailed nameMap errs = do
  src <- getImportSource
  ModuleT (raise (TypeCheckingFailed src nameMap errs))

moduleNameMismatch :: P.ModName -> Located P.ModName -> ModuleM a
moduleNameMismatch expected found =
  ModuleT (raise (ModuleNameMismatch expected found))

duplicateModuleName :: P.ModName -> FilePath -> FilePath -> ModuleM a
duplicateModuleName name path1 path2 =
  ModuleT (raise (DuplicateModuleName name path1 path2))

ffiLoadErrors :: P.ModName -> [FFILoadError] -> ModuleM a
ffiLoadErrors x errs = ModuleT (raise (FFILoadErrors x errs))

-- | Run the computation, and if it caused and error, tag the error
-- with the given file.
errorInFile :: ModulePath -> ModuleM a -> ModuleM a
errorInFile file (ModuleT m) = ModuleT (m `handle` h)
  where h e = raise $ case e of
                        ErrorInFile {} -> e
                        _              -> ErrorInFile file e

tryModule :: ModuleM a -> ModuleM (Either ModuleError a)
tryModule (ModuleT m) = ModuleT (handle (Right <$> m) (pure . Left))

-- Warnings --------------------------------------------------------------------

data ModuleWarning
  = TypeCheckWarnings T.NameMap [(Range,T.Warning)]
  | RenamerWarnings [RenamerWarning]
    deriving (Show, Generic, NFData)

instance PP ModuleWarning where
  ppPrec _ w = case w of
    TypeCheckWarnings nm ws -> vcat (map (T.ppNamedWarning nm) ws)
    RenamerWarnings ws   -> vcat (map pp ws)

warn :: [ModuleWarning] -> ModuleM ()
warn  = ModuleT . put

typeCheckWarnings :: T.NameMap -> [(Range,T.Warning)] -> ModuleM ()
typeCheckWarnings nameMap ws
  | null ws   = return ()
  | otherwise = warn [TypeCheckWarnings nameMap ws]

renamerWarnings :: [RenamerWarning] -> ModuleM ()
renamerWarnings ws
  | null ws   = return ()
  | otherwise = warn [RenamerWarnings ws]


-- Module System Monad ---------------------------------------------------------

data RO m =
  RO { roLoading    :: [ImportSource]
     , roEvalOpts   :: m EvalOpts
     , roCallStacks :: Bool
     , roFileReader :: FilePath -> m ByteString
     , roTCSolver   :: SMT.Solver
     }

emptyRO :: ModuleInput m -> RO m
emptyRO minp =
  RO { roLoading = []
     , roEvalOpts   = minpEvalOpts minp
     , roCallStacks = minpCallStacks minp
     , roFileReader = minpByteReader minp
     , roTCSolver   = minpTCSolver minp
     }

newtype ModuleT m a = ModuleT
  { unModuleT :: ReaderT (RO m)
                   (StateT ModuleEnv
                     (ExceptionT ModuleError
                       (WriterT [ModuleWarning] m))) a
  }

instance Monad m => Functor (ModuleT m) where
  {-# INLINE fmap #-}
  fmap f m      = ModuleT (fmap f (unModuleT m))

instance Monad m => Applicative (ModuleT m) where
  {-# INLINE pure #-}
  pure x = ModuleT (pure x)

  {-# INLINE (<*>) #-}
  l <*> r = ModuleT (unModuleT l <*> unModuleT r)

instance Monad m => Monad (ModuleT m) where
  {-# INLINE return #-}
  return        = pure

  {-# INLINE (>>=) #-}
  m >>= f       = ModuleT (unModuleT m >>= unModuleT . f)

instance Fail.MonadFail m => Fail.MonadFail (ModuleT m) where
  {-# INLINE fail #-}
  fail          = ModuleT . raise . OtherFailure

instance MonadT ModuleT where
  {-# INLINE lift #-}
  lift = ModuleT . lift . lift . lift . lift

instance Monad m => FreshM (ModuleT m) where
  liftSupply f = ModuleT $
    do me <- get
       let (a,s') = f (meSupply me)
       set $! me { meSupply = s' }
       return a

instance MonadIO m => MonadIO (ModuleT m) where
  liftIO m = lift $ liftIO m


data ModuleInput m =
  ModuleInput
  { minpCallStacks :: Bool
  , minpEvalOpts   :: m EvalOpts
  , minpByteReader :: FilePath -> m ByteString
  , minpModuleEnv  :: ModuleEnv
  , minpTCSolver   :: SMT.Solver
  }

runModuleT ::
  Monad m =>
  ModuleInput m ->
  ModuleT m a ->
  m (Either ModuleError (a, ModuleEnv), [ModuleWarning])
runModuleT minp m =
    runWriterT
  $ runExceptionT
  $ runStateT (minpModuleEnv minp)
  $ runReaderT (emptyRO minp)
  $ unModuleT m

type ModuleM = ModuleT IO

runModuleM ::
  ModuleInput IO ->
  ModuleM a ->
  IO (Either ModuleError (a,ModuleEnv),[ModuleWarning])
runModuleM = runModuleT


io :: BaseM m IO => IO a -> ModuleT m a
io m = ModuleT (inBase m)

getByteReader :: Monad m => ModuleT m (FilePath -> m ByteString)
getByteReader = ModuleT $ do
  RO { roFileReader = readFileBytes } <- ask
  return readFileBytes

getCallStacks :: Monad m => ModuleT m Bool
getCallStacks = ModuleT (roCallStacks <$> ask)

readBytes :: Monad m => FilePath -> ModuleT m ByteString
readBytes fn = do
  fileReader <- getByteReader
  ModuleT $ lift $ lift $ lift $ lift $ fileReader fn

getModuleEnv :: Monad m => ModuleT m ModuleEnv
getModuleEnv = ModuleT get

getTCSolver :: Monad m => ModuleT m SMT.Solver
getTCSolver = ModuleT (roTCSolver <$> ask)

setModuleEnv :: Monad m => ModuleEnv -> ModuleT m ()
setModuleEnv = ModuleT . set

modifyModuleEnv :: Monad m => (ModuleEnv -> ModuleEnv) -> ModuleT m ()
modifyModuleEnv f = ModuleT $ do
  env <- get
  set $! f env

getLoadedMaybe :: P.ModName -> ModuleM (Maybe (LoadedModuleG T.TCTopEntity))
getLoadedMaybe mn = ModuleT $
  do env <- get
     return (lookupTCEntity mn env)

-- | This checks if the given name is loaded---it might refer to either
-- a module or a signature.
isLoaded :: P.ModName -> ModuleM Bool
isLoaded mn =
  do env <- ModuleT get
     pure (MEnv.isLoaded (T.ImpTop mn) (meLoadedModules env))

isLoadedStrict :: P.ModName -> ModulePath -> ModuleM Bool
isLoadedStrict mn mpath =
  do env <- ModuleT get
     pure (MEnv.isLoadedStrict (T.ImpTop mn) (modulePathLabel mpath) (meLoadedModules env))

loadingImport :: Located P.Import -> ModuleM a -> ModuleM a
loadingImport  = loading . FromImport

loadingModule :: P.ModName -> ModuleM a -> ModuleM a
loadingModule  = loading . FromModule

loadingModInstance :: Located P.ModName -> ModuleM a -> ModuleM a
loadingModInstance = loading . FromModuleInstance

-- | Push an "interactive" context onto the loading stack.  A bit of a hack, as
-- it uses a faked module name
interactive :: ModuleM a -> ModuleM a
interactive  = loadingModule interactiveName

loading :: ImportSource -> ModuleM a -> ModuleM a
loading src m = ModuleT $ do
  ro <- ask
  let new = src : roLoading ro

  -- check for recursive modules
  when (src `elem` roLoading ro) (raise (RecursiveModules new))

  local ro { roLoading = new } (unModuleT m)

-- | Get the currently focused import source.
getImportSource :: ModuleM ImportSource
getImportSource  = ModuleT $ do
  ro <- ask
  case roLoading ro of
    is : _ -> return is
    _      -> return (FromModule noModuleName)

getIfaces :: ModuleM (Map P.ModName (Either T.ModParamNames Iface))
getIfaces = toMap <$> ModuleT get
  where
  toMap env = cvt <$> getLoadedEntities (meLoadedModules env)

  cvt ent =
    case ent of
      ALoadedInterface ifa -> Left (lmData ifa)
      ALoadedFunctor mo -> Right (lmdInterface (lmData mo))
      ALoadedModule mo -> Right (lmdInterface (lmData mo))

getLoaded :: P.ModName -> ModuleM T.Module
getLoaded mn = ModuleT $
  do env <- get
     case lookupModule mn env of
       Just lm -> return (lmModule lm)
       Nothing -> panic "ModuleSystem" ["Module not available", show (pp mn) ]

getAllLoaded :: ModuleM (P.ModName -> Maybe (T.ModuleG (), IfaceG ()))
getAllLoaded = ModuleT
  do env <- get
     pure \nm -> do lm <- lookupModule nm env
                    pure ( (lmModule lm) { T.mName = () }
                         , ifaceForgetName (lmInterface lm)
                         )

getAllLoadedSignatures :: ModuleM (P.ModName -> Maybe T.ModParamNames)
getAllLoadedSignatures = ModuleT
  do env <- get
     pure \nm -> lmData <$> lookupSignature nm env


getNameSeeds :: ModuleM T.NameSeeds
getNameSeeds  = ModuleT (meNameSeeds `fmap` get)

getSupply :: ModuleM Supply
getSupply  = ModuleT (meSupply `fmap` get)

getMonoBinds :: ModuleM Bool
getMonoBinds  = ModuleT (meMonoBinds `fmap` get)

getEvalForeignPolicy :: ModuleM EvalForeignPolicy
getEvalForeignPolicy = ModuleT (meEvalForeignPolicy <$> get)

setMonoBinds :: Bool -> ModuleM ()
setMonoBinds b = ModuleT $ do
  env <- get
  set $! env { meMonoBinds = b }

setNameSeeds :: T.NameSeeds -> ModuleM ()
setNameSeeds seeds = ModuleT $ do
  env <- get
  set $! env { meNameSeeds = seeds }

setSupply :: Supply -> ModuleM ()
setSupply supply = ModuleT $
  do env <- get
     set $! env { meSupply = supply }

unloadModule :: (forall a. LoadedModuleG a -> Bool) -> ModuleM ()
unloadModule rm = ModuleT $ do
  env <- get
  set $! env { meLoadedModules = removeLoadedModule rm (meLoadedModules env) }

loadedModule ::
  ModulePath ->
  FileInfo ->
  NamingEnv ->
  Maybe ForeignSrc ->
  T.TCTopEntity ->
  ModuleM ()
loadedModule path fi nameEnv fsrc m = ModuleT $ do
  env <- get
  ident <- case path of
             InFile p  -> unModuleT $ io (canonicalizePath p)
             InMem l _ -> pure l

  let newLM =
        case m of
          T.TCTopModule mo -> addLoadedModule path ident fi nameEnv fsrc mo
          T.TCTopSignature x s -> addLoadedSignature path ident fi nameEnv x s

  set $! env { meLoadedModules = newLM (meLoadedModules env) }


modifyEvalEnvM :: Traversable t =>
  (EvalEnv -> E.Eval (t EvalEnv)) -> ModuleM (t ())
modifyEvalEnvM f = ModuleT $ do
  env <- get
  let evalEnv = meEvalEnv env
  tenv <- inBase (E.runEval mempty (f evalEnv))
  traverse (\evalEnv' -> set $! env { meEvalEnv = evalEnv' }) tenv

modifyEvalEnv :: (EvalEnv -> E.Eval EvalEnv) -> ModuleM ()
modifyEvalEnv = fmap runIdentity . modifyEvalEnvM . (fmap Identity .)

getEvalEnv :: ModuleM EvalEnv
getEvalEnv  = ModuleT (meEvalEnv `fmap` get)

getEvalOptsAction :: ModuleM (IO EvalOpts)
getEvalOptsAction = ModuleT (roEvalOpts `fmap` ask)

getEvalOpts :: ModuleM EvalOpts
getEvalOpts =
  do act <- getEvalOptsAction
     liftIO act

getNominalTypes :: ModuleM (Map T.Name T.NominalType)
getNominalTypes = ModuleT (loadedNominalTypes <$> get)

getFocusedModule :: ModuleM (Maybe (P.ImpName T.Name))
getFocusedModule  = ModuleT (meFocusedModule `fmap` get)

setFocusedModule :: P.ImpName T.Name -> ModuleM ()
setFocusedModule = setMaybeFocusedModule . Just

setMaybeFocusedModule :: Maybe (P.ImpName T.Name) -> ModuleM ()
setMaybeFocusedModule mb = ModuleT $ do
  me <- get
  set $! me { meFocusedModule = mb }

getSearchPath :: ModuleM [FilePath]
getSearchPath  = ModuleT (meSearchPath `fmap` get)

-- | Run a 'ModuleM' action in a context with a prepended search
-- path. Useful for temporarily looking in other places while
-- resolving imports, for example.
withPrependedSearchPath :: [FilePath] -> ModuleM a -> ModuleM a
withPrependedSearchPath fps m = ModuleT $ do
  env0 <- get
  let fps0 = meSearchPath env0
  set $! env0 { meSearchPath = fps ++ fps0 }
  x <- unModuleT m
  env <- get
  set $! env { meSearchPath = fps0 }
  return x

getFocusedEnv :: ModuleM ModContext
getFocusedEnv  = ModuleT (focusedEnv `fmap` get)

getDynEnv :: ModuleM DynamicEnv
getDynEnv  = ModuleT (meDynEnv `fmap` get)

setDynEnv :: DynamicEnv -> ModuleM ()
setDynEnv denv = ModuleT $ do
  me <- get
  set $! me { meDynEnv = denv }

-- | Usefule for logging.  For example: @withLogger logPutStrLn "Hello"@
withLogger :: (Logger -> a -> IO b) -> a -> ModuleM b
withLogger f a = do l <- getEvalOpts
                    io (f (evalLogger l) a)

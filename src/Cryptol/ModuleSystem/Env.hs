-- |
-- Module      :  Cryptol.ModuleSystem.Env
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
module Cryptol.ModuleSystem.Env where

#ifndef RELOCATABLE
import Paths_cryptol (getDataDir)
#endif

import Cryptol.Eval.FFI.ForeignSrc(ForeignSrc, unloadForeignSrc, getForeignSrcPath)
import Cryptol.Eval (EvalEnv)
import qualified Cryptol.IR.FreeVars as T
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name (Name,NameInfo(..),Supply,emptySupply,nameInfo,nameTopModuleMaybe)
import qualified Cryptol.ModuleSystem.NamingEnv as R
import Cryptol.Parser.AST
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.Interface as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.Utils.Ident as I
import Cryptol.Utils.PP (PP(..),text,parens,NameDisp)

import Data.ByteString(ByteString)
import Control.Monad (guard,mplus)
import qualified Control.Exception as X
import Data.Function (on)
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup
import Data.Maybe(fromMaybe)
import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import System.Environment(getExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, takeDirectory)
import qualified Data.List as List
import Data.Foldable

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.PP(pp)

-- Module Environment ----------------------------------------------------------

-- | This is the current state of the interpreter.
data ModuleEnv = ModuleEnv
  { meLoadedModules     :: LoadedModules
    -- ^ Information about all loaded modules.  See 'LoadedModule'.
    -- Contains information such as the file where the module was loaded
    -- from, as well as the module's interface, used for type checking.

  , meNameSeeds         :: T.NameSeeds
    -- ^ A source of new names for the type checker.

  , meEvalEnv           :: EvalEnv
    -- ^ The evaluation environment.  Contains the values for all loaded
    -- modules, both public and private.

  , meCoreLint          :: CoreLint
    -- ^ Should we run the linter to ensure sanity.

  , meMonoBinds         :: !Bool
    -- ^ Are we assuming that local bindings are monomorphic.
    -- XXX: We should probably remove this flag, and set it to 'True'.



  , meFocusedModule     :: Maybe (ImpName Name)
    -- ^ The "current" module.  Used to decide how to print names, for example.

  , meSearchPath        :: [FilePath]
    -- ^ Where we look for things.

  , meDynEnv            :: DynamicEnv
    -- ^ This contains additional definitions that were made at the command
    -- line, and so they don't reside in any module.

  , meSupply            :: !Supply
    -- ^ Name source for the renamer

  , meEvalForeignPolicy :: EvalForeignPolicy
    -- ^ How to evaluate @foreign@ bindings.

  } deriving Generic

instance NFData ModuleEnv where
  rnf x = meLoadedModules x `seq` meEvalEnv x `seq` meDynEnv x `seq` ()

-- | Should we run the linter?
data CoreLint = NoCoreLint        -- ^ Don't run core lint
              | CoreLint          -- ^ Run core lint
  deriving (Generic, NFData)

-- | How to evaluate @foreign@ bindings.
data EvalForeignPolicy
  -- | Use foreign implementation and report an error at module load time if it
  -- is unavailable.
  = AlwaysEvalForeign
  -- | Use foreign implementation by default, and when unavailable, fall back to cryptol implementation if present and report runtime error otherwise.
  | PreferEvalForeign
  -- | Always use cryptol implementation if present, and report runtime error
  -- otherwise.
  | NeverEvalForeign
  deriving Eq

defaultEvalForeignPolicy :: EvalForeignPolicy
defaultEvalForeignPolicy =
#ifdef FFI_ENABLED
  PreferEvalForeign
#else
  NeverEvalForeign
#endif

resetModuleEnv :: ModuleEnv -> IO ModuleEnv
resetModuleEnv env = do
  for_ (getLoadedModules $ meLoadedModules env) $ \lm ->
    case lmForeignSrc (lmData lm) of
      Just fsrc -> unloadForeignSrc fsrc
      _         -> pure ()
  pure env
    { meLoadedModules = mempty
    , meNameSeeds     = T.nameSeeds
    , meEvalEnv       = mempty
    , meFocusedModule = Nothing
    , meDynEnv        = mempty
    }

initialModuleEnv :: IO ModuleEnv
initialModuleEnv = do
  curDir <- getCurrentDirectory
#ifndef RELOCATABLE
  dataDir <- getDataDir
#endif
  binDir <- takeDirectory `fmap` getExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  -- looking up this directory can fail if no HOME is set, as in some
  -- CI settings
  let handle :: X.IOException -> IO String
      handle _e = return ""
  userDir <- X.catch (getAppUserDataDirectory "cryptol") handle
  let searchPath = [ curDir
                   -- something like $HOME/.cryptol
                   , userDir
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
                   -- ../cryptol on win32
                   , instDir </> "cryptol"
#else
                   -- ../share/cryptol on others
                   , instDir </> "share" </> "cryptol"
#endif

#ifndef RELOCATABLE
                   -- Cabal-defined data directory. Since this
                   -- is usually a global location like
                   -- /usr/local, search this one last in case
                   -- someone has multiple Cryptols
                   , dataDir
#endif
                   ]

  return ModuleEnv
    { meLoadedModules     = mempty
    , meNameSeeds         = T.nameSeeds
    , meEvalEnv           = mempty
    , meFocusedModule     = Nothing
      -- we search these in order, taking the first match
    , meSearchPath        = searchPath
    , meDynEnv            = mempty
    , meMonoBinds         = True
    , meCoreLint          = NoCoreLint
    , meSupply            = emptySupply
    , meEvalForeignPolicy = defaultEvalForeignPolicy
    }

-- | Try to focus a loaded module in the module environment.
focusModule :: ImpName Name -> ModuleEnv -> Maybe ModuleEnv
focusModule n me = do
  guard (isLoaded n (meLoadedModules me))
  return me { meFocusedModule = Just n }

-- | Get a list of all the loaded modules. Each module in the
-- resulting list depends only on other modules that precede it.
-- Note that this includes parameterized modules.
loadedModules :: ModuleEnv -> [T.Module]
loadedModules = map lmModule . getLoadedModules . meLoadedModules

-- | Get a list of all the loaded non-parameterized modules.
-- These are the modules that can be used for evaluation, proving etc.
loadedNonParamModules :: ModuleEnv -> [T.Module]
loadedNonParamModules = map lmModule . lmLoadedModules . meLoadedModules

loadedNominalTypes :: ModuleEnv -> Map Name T.NominalType
loadedNominalTypes menv = Map.unions
   [ ifNominalTypes (ifDefines i) <> ifNominalTypes (ifDefines i)
   | i <- map lmInterface (getLoadedModules (meLoadedModules menv))
   ]

-- | Are any parameterized modules loaded?
hasParamModules :: ModuleEnv -> Bool
hasParamModules = not . null . lmLoadedParamModules . meLoadedModules

allDeclGroups :: ModuleEnv -> [T.DeclGroup]
allDeclGroups = concatMap T.mDecls . loadedNonParamModules

data ModContextParams =
    InterfaceParams T.ModParamNames
  | FunctorParams T.FunctorParams
  | NoParams

modContextParamNames :: ModContextParams -> T.ModParamNames
modContextParamNames mp =
  case mp of
    InterfaceParams ps -> ps
    FunctorParams ps   -> T.allParamNames ps
    NoParams           -> T.allParamNames mempty

-- | Contains enough information to browse what's in scope,
-- or type check new expressions.
data ModContext = ModContext
  { mctxParams          :: ModContextParams -- T.FunctorParams
  , mctxExported        :: Set Name
  , mctxDecls           :: IfaceDecls
    -- ^ Should contain at least names in NamingEnv, but may have more
  , mctxNames           :: R.NamingEnv
    -- ^ What's in scope inside the module
  , mctxNameDisp        :: NameDisp
  }

-- This instance is a bit bogus.  It is mostly used to add the dynamic
-- environemnt to an existing module, and it makes sense for that use case.
instance Semigroup ModContext where
  x <> y = ModContext { mctxParams   = jnPs (mctxParams x) (mctxParams y)
                      , mctxExported = mctxExported x <> mctxExported y
                      , mctxDecls    = mctxDecls x  <> mctxDecls  y
                      , mctxNames    = names
                      , mctxNameDisp = R.toNameDisp names
                      }

      where
      names = mctxNames x `R.shadowing` mctxNames y
      jnPs as bs =
        case (as,bs) of
          (NoParams,_) -> bs
          (_,NoParams) -> as
          (FunctorParams xs, FunctorParams ys) -> FunctorParams (xs <> ys)
          _ -> panic "(<>) @ ModContext" ["Can't combine parameters"]

instance Monoid ModContext where
  mempty = ModContext { mctxParams   = NoParams
                      , mctxDecls    = mempty
                      , mctxExported = mempty
                      , mctxNames    = mempty
                      , mctxNameDisp = R.toNameDisp mempty
                      }

findEnv :: Name -> Iface -> T.ModuleG a -> Maybe (R.NamingEnv, Set Name)
findEnv n iface m
  | Just sm <- Map.lookup n (T.mSubmodules m) = Just (T.smInScope sm, ifsPublic (T.smIface sm))
  | Just fn <- Map.lookup n (T.mFunctors m) =
      case Map.lookup n (ifFunctors (ifDefines iface)) of
        Nothing -> panic "findEnv" ["Submodule functor not present in interface"]
        Just d -> Just (T.mInScope fn, ifsPublic (ifNames d))
  | otherwise = asum (fmap (findEnv n iface) (Map.elems (T.mFunctors m)))

modContextOf :: ImpName Name -> ModuleEnv -> Maybe ModContext
modContextOf (ImpNested name) me =
  do mname <- nameTopModuleMaybe name
     lm <- lookupModule mname me
     (localNames, exported) <- findEnv name (lmInterface lm) (lmModule lm)
     let -- XXX: do we want only public ones here?
         loadedDecls = map (ifDefines . lmInterface)
                     $ getLoadedModules (meLoadedModules me)
     pure ModContext
       { mctxParams   = NoParams
       , mctxExported = exported
       , mctxDecls    = mconcat (ifDefines (lmInterface lm) : loadedDecls)
       , mctxNames    = localNames
       , mctxNameDisp = R.toNameDisp localNames
       }
  -- TODO: support focusing inside a submodule signature to support browsing?

modContextOf (ImpTop mname) me =
  do lm <- lookupModule mname me
     let localIface  = lmInterface lm
         localNames  = lmNamingEnv lm

         -- XXX: do we want only public ones here?
         loadedDecls = map (ifDefines . lmInterface)
                     $ getLoadedModules (meLoadedModules me)

         params = ifParams localIface
     pure ModContext
       { mctxParams   = if Map.null params then NoParams
                                           else FunctorParams params
       , mctxExported = ifsPublic (ifNames localIface)
       , mctxDecls    = mconcat (ifDefines localIface : loadedDecls)
       , mctxNames    = localNames
       , mctxNameDisp = R.toNameDisp localNames
       }
  `mplus`
  do lm <- lookupSignature mname me
     let localNames  = lmNamingEnv lm
         -- XXX: do we want only public ones here?
         loadedDecls = map (ifDefines . lmInterface)
                     $ getLoadedModules (meLoadedModules me)
     pure ModContext
       { mctxParams   = InterfaceParams (lmData lm)
       , mctxExported = Set.empty
       , mctxDecls    = mconcat loadedDecls
       , mctxNames    = localNames
       , mctxNameDisp = R.toNameDisp localNames
       }



dynModContext :: ModuleEnv -> ModContext
dynModContext me = mempty { mctxNames    = dynNames
                          , mctxNameDisp = R.toNameDisp dynNames
                          , mctxDecls    = deIfaceDecls (meDynEnv me)
                          }
  where dynNames = deNames (meDynEnv me)




-- | Given the state of the environment, compute information about what's
-- in scope on the REPL.  This includes what's in the focused module, plus any
-- additional definitions from the REPL (e.g., let bound names, and @it@).
focusedEnv :: ModuleEnv -> ModContext
focusedEnv me =
  case meFocusedModule me of
    Nothing -> dynModContext me
    Just fm -> case modContextOf fm me of
                 Just c -> dynModContext me <> c
                 Nothing -> panic "focusedEnv"
                              [ "Focused modules not loaded: " ++ show (pp fm) ]


-- Loaded Modules --------------------------------------------------------------

-- | The location of a module
data ModulePath = InFile FilePath
                | InMem String ByteString -- ^ Label, content
    deriving (Show, Read, Generic, NFData)

-- | In-memory things are compared by label.
instance Eq ModulePath where
  p1 == p2 =
    case (p1,p2) of
      (InFile x, InFile y) -> x == y
      (InMem a _, InMem b _) -> a == b
      _ -> False

-- | In-memory things are compared by label.
instance Ord ModulePath where
  compare p1 p2 =
    case (p1,p2) of
      (InFile x, InFile y)   -> compare x y
      (InMem a _, InMem b _) -> compare a b
      (InMem {}, InFile {})  -> LT
      (InFile {}, InMem {})  -> GT



instance PP ModulePath where
  ppPrec _ e =
    case e of
      InFile p  -> text p
      InMem l _ -> parens (text l)



-- | The name of the content---either the file path, or the provided label.
modulePathLabel :: ModulePath -> String
modulePathLabel p =
  case p of
    InFile path -> path
    InMem lab _ -> lab



data LoadedModules = LoadedModules
  { lmLoadedModules      :: [LoadedModule]
    -- ^ Invariants:
    -- 1) All the dependencies of any module `m` must precede `m` in the list.
    -- 2) Does not contain any parameterized modules.

  , lmLoadedParamModules :: [LoadedModule]
    -- ^ Loaded parameterized modules.

  , lmLoadedSignatures :: ![LoadedSignature]

  } deriving (Show, Generic, NFData)

data LoadedEntity =
    ALoadedModule LoadedModule
  | ALoadedFunctor LoadedModule
  | ALoadedInterface LoadedSignature

getLoadedEntities ::
  LoadedModules -> Map ModName LoadedEntity
getLoadedEntities lm =
  Map.fromList $ [ (lmName x, ALoadedModule x) | x <- lmLoadedModules lm ] ++
                 [ (lmName x, ALoadedFunctor x) | x <- lmLoadedParamModules lm ] ++
                 [ (lmName x, ALoadedInterface x) | x <- lmLoadedSignatures lm ]

getLoadedModules :: LoadedModules -> [LoadedModule]
getLoadedModules x = lmLoadedParamModules x ++ lmLoadedModules x

getLoadedField :: Ord a =>
  (forall b. LoadedModuleG b -> a) -> LoadedModules -> Set a
getLoadedField f lm = Set.fromList
                    $ map f (lmLoadedModules lm)
                   ++ map f (lmLoadedParamModules lm)
                   ++ map f (lmLoadedSignatures lm)

getLoadedNames :: LoadedModules -> Set ModName
getLoadedNames = getLoadedField lmName

getLoadedIds :: LoadedModules -> Set String
getLoadedIds = getLoadedField lmModuleId

instance Semigroup LoadedModules where
  l <> r = LoadedModules
    { lmLoadedModules = List.unionBy ((==) `on` lmName)
                                      (lmLoadedModules l) (lmLoadedModules r)
    , lmLoadedParamModules = lmLoadedParamModules l ++ lmLoadedParamModules r
    , lmLoadedSignatures   = lmLoadedSignatures l ++ lmLoadedSignatures r
    }

instance Monoid LoadedModules where
  mempty = LoadedModules { lmLoadedModules = []
                         , lmLoadedParamModules = []
                         , lmLoadedSignatures = []
                         }
  mappend = (<>)

-- | A generic type for loaded things.
-- The things can be either modules or signatures.
data LoadedModuleG a = LoadedModule
  { lmName              :: ModName
    -- ^ The name of this module.  Should match what's in 'lmModule'

  , lmFilePath          :: ModulePath
    -- ^ The file path used to load this module (may not be canonical)

  , lmModuleId          :: String
    -- ^ An identifier used to identify the source of the bytes for the module.
    -- For files we just use the cononical path, for in memory things we
    -- use their label.

  , lmNamingEnv         :: !R.NamingEnv
    -- ^ What's in scope in this module

  , lmFileInfo          :: !FileInfo

  , lmRenamedModule     :: Maybe (Module Name)
    -- ^ The renamed AST, if we chose to save it

  , lmData              :: a
  } deriving (Show, Generic, NFData)

type LoadedModule = LoadedModuleG LoadedModuleData

lmModule :: LoadedModule -> T.Module
lmModule = lmdModule . lmData

lmInterface :: LoadedModule -> Iface
lmInterface = lmdInterface . lmData

data LoadedModuleData = LoadedModuleData
  { lmdInterface         :: Iface
    -- ^ The module's interface.

  , lmdModule            :: T.Module
    -- ^ The actual type-checked module

  , lmForeignSrc        :: Maybe ForeignSrc
    -- ^ The dynamically loaded source for any foreign functions in the module
  } deriving (Show, Generic, NFData)

type LoadedSignature = LoadedModuleG T.ModParamNames


-- | Has this module been loaded already.
isLoaded :: ImpName Name -> LoadedModules -> Bool
isLoaded (ImpTop mn) lm = mn `Set.member` getLoadedNames lm
isLoaded (ImpNested nn) lm = any (check . lmModule) (getLoadedModules lm)
  where
    check :: T.ModuleG a -> Bool
    check m =
      Map.member nn (T.mSubmodules m) ||
      Map.member nn (T.mSignatures m) ||
      Map.member nn (T.mSubmodules m) ||
      any check (T.mFunctors m)

isLoadedStrict :: ImpName Name -> String -> LoadedModules -> Bool
isLoadedStrict mn modId lm =
  isLoaded mn lm && modId `Set.member` getLoadedIds lm

-- | Is this a loaded parameterized module.
isLoadedParamMod :: ImpName Name -> LoadedModules -> Bool
isLoadedParamMod (ImpTop mn) lm = any ((mn ==) . lmName) (lmLoadedParamModules lm)
isLoadedParamMod (ImpNested n) lm =
  any (check1 . lmModule) (lmLoadedModules lm) ||
  any (check2 . lmModule) (lmLoadedParamModules lm)
  where
    -- We haven't crossed into a parameterized functor yet
    check1 m = Map.member n (T.mFunctors m)
            || any check2 (T.mFunctors m)

    -- We're inside a parameterized module and are finished as soon as we have containment
    check2 :: T.ModuleG a -> Bool
    check2 m =
      Map.member n (T.mSubmodules m) ||
      Map.member n (T.mSignatures m) ||
      Map.member n (T.mFunctors m) ||
      any check2 (T.mFunctors m)

-- | Is this a loaded interface module.
isLoadedInterface :: ImpName Name -> LoadedModules -> Bool
isLoadedInterface (ImpTop mn) ln = any ((mn ==) . lmName) (lmLoadedSignatures ln)
isLoadedInterface (ImpNested nn) ln = any (check . lmModule) (getLoadedModules ln)
  where
    check :: T.ModuleG a -> Bool
    check m =
      Map.member nn (T.mSignatures m) ||
      any check (T.mFunctors m)

-- | Return the set of type parameters (@'Set' 'T.TParam'@) and definitions
-- (@'Set' 'Name'@) from the supplied 'LoadedModules' value that another
-- definition (of type @a@) depends on.
loadedParamModDeps ::
  T.FreeVars a =>
  LoadedModules ->
  a ->
  (Set T.TParam, Set Name)
loadedParamModDeps lm a = (badTs, bad)
  where
    ds      = T.freeVars a
    badVals = foldr badName Set.empty (T.valDeps ds)
    bad     = foldr badName badVals (T.tyDeps ds)
    badTs   = T.tyParams ds

    badName nm bs =
      case nameInfo nm of

        -- XXX: Changes if focusing on nested modules
        GlobalName _ I.OrigName { ogModule = I.TopModule m }
          | isLoadedParamMod (ImpTop m) lm -> Set.insert nm bs
          | isLoadedInterface (ImpTop m) lm -> Set.insert nm bs

        _ -> bs


lookupTCEntity :: ModName -> ModuleEnv -> Maybe (LoadedModuleG T.TCTopEntity)
lookupTCEntity m env =
  case lookupModule m env of
    Just lm -> pure lm { lmData = T.TCTopModule (lmModule lm) }
    Nothing ->
      do lm <- lookupSignature m env
         pure lm { lmData = T.TCTopSignature m (lmData lm) }

-- | Try to find a previously loaded module
lookupModule :: ModName -> ModuleEnv -> Maybe LoadedModule
lookupModule mn = lookupModuleWith ((mn ==) . lmName)

lookupModuleWith :: (LoadedModule -> Bool) -> ModuleEnv -> Maybe LoadedModule
lookupModuleWith p me =
  search lmLoadedModules `mplus` search lmLoadedParamModules
  where
  search how = List.find p (how (meLoadedModules me))

lookupSignature :: ModName -> ModuleEnv -> Maybe LoadedSignature
lookupSignature mn = lookupSignatureWith ((mn ==) . lmName)

lookupSignatureWith ::
  (LoadedSignature -> Bool) -> ModuleEnv -> Maybe LoadedSignature
lookupSignatureWith p me = List.find p (lmLoadedSignatures (meLoadedModules me))

addLoadedSignature ::
  ModulePath -> String ->
  FileInfo ->
  R.NamingEnv ->
  ModName -> Maybe (Module T.Name) -> T.ModParamNames ->
  LoadedModules -> LoadedModules
addLoadedSignature path ident fi nameEnv nm rm si lm
  | isLoadedStrict (ImpTop nm) ident lm = lm
  | otherwise = lm { lmLoadedSignatures = loaded : lmLoadedSignatures lm }
  where
  loaded = LoadedModule
            { lmName        = nm
            , lmFilePath    = path
            , lmModuleId    = ident
            , lmNamingEnv   = nameEnv
            , lmData        = si
            , lmFileInfo    = fi
            , lmRenamedModule = rm
            }

-- | Add a freshly loaded module.  If it was previously loaded, then
-- the new version is ignored.
addLoadedModule ::
  ModulePath ->
  String ->
  FileInfo ->
  R.NamingEnv ->
  Maybe ForeignSrc ->
  Maybe (Module T.Name) ->
  T.Module -> LoadedModules -> LoadedModules
addLoadedModule path ident fi nameEnv fsrc rm tm lm
  | isLoadedStrict (ImpTop (T.mName tm)) ident lm = lm
  | T.isParametrizedModule tm = lm { lmLoadedParamModules = loaded :
                                                lmLoadedParamModules lm }
  | otherwise                = lm { lmLoadedModules =
                                          lmLoadedModules lm ++ [loaded] }
  where
  loaded = LoadedModule
    { lmName            = T.mName tm
    , lmFilePath        = path
    , lmModuleId        = ident
    , lmNamingEnv       = nameEnv
    , lmRenamedModule   = rm
    , lmData            = LoadedModuleData
                             { lmdInterface = T.genIface tm
                             , lmdModule    = tm
                             , lmForeignSrc = fsrc
                             }
    , lmFileInfo        = fi
    }

-- | Remove a previously loaded module.
-- Note that this removes exactly the modules specified by the predicate.
-- One should be carfule to preserve the invariant on 'LoadedModules'.
removeLoadedModule ::
  (forall a. LoadedModuleG a -> Bool) -> LoadedModules -> LoadedModules
removeLoadedModule rm lm =
  LoadedModules
    { lmLoadedModules       = filter (not . rm) (lmLoadedModules lm)
    , lmLoadedParamModules  = filter (not . rm) (lmLoadedParamModules lm)
    , lmLoadedSignatures    = filter (not . rm) (lmLoadedSignatures lm)
    }

-- FileInfo --------------------------------------------------------------------

data FileInfo = FileInfo
  { fiFingerprint :: Fingerprint
  , fiIncludeDeps :: Map FilePath Fingerprint
  , fiImportDeps  :: Set ModName
  , fiForeignDeps :: Map FilePath Bool
    -- ^ The bool indicates if the library for the foreign import exists.
  } deriving (Show,Generic,NFData)


fileInfo ::
  Fingerprint ->
  Map FilePath Fingerprint ->
  Set ModName ->
  Maybe ForeignSrc ->
  FileInfo
fileInfo fp incDeps impDeps fsrc =
  FileInfo
    { fiFingerprint = fp
    , fiIncludeDeps = incDeps
    , fiImportDeps  = impDeps
    , fiForeignDeps = fromMaybe Map.empty
                      do src <- fsrc
                         fpath <- getForeignSrcPath src
                         pure $ Map.singleton fpath True
    }


-- Dynamic Environments --------------------------------------------------------

-- | Extra information we need to carry around to dynamically extend
-- an environment outside the context of a single module. Particularly
-- useful when dealing with interactive declarations as in @let@ or
-- @it@.
data DynamicEnv = DEnv
  { deNames :: R.NamingEnv
  , deDecls :: [T.DeclGroup]
  , deTySyns :: Map Name T.TySyn
  , deEnv   :: EvalEnv
  } deriving Generic

instance Semigroup DynamicEnv where
  de1 <> de2 = DEnv
    { deNames  = deNames de1  <> deNames de2
    , deDecls  = deDecls de1  <> deDecls de2
    , deTySyns = deTySyns de1 <> deTySyns de2
    , deEnv    = deEnv   de1  <> deEnv   de2
    }

instance Monoid DynamicEnv where
  mempty = DEnv
    { deNames  = mempty
    , deDecls  = mempty
    , deTySyns = mempty
    , deEnv    = mempty
    }
  mappend = (<>)

-- | Build 'IfaceDecls' that correspond to all of the bindings in the
-- dynamic environment.
--
-- XXX: if we add newtypes, etc. at the REPL, revisit
-- this.
deIfaceDecls :: DynamicEnv -> IfaceDecls
deIfaceDecls DEnv { deDecls = dgs, deTySyns = tySyns } =
    IfaceDecls { ifTySyns = tySyns
               , ifNominalTypes = Map.empty
               , ifDecls = decls
               , ifModules = Map.empty
               , ifFunctors = Map.empty
               , ifSignatures = Map.empty
               }
  where
    decls = mconcat
      [ Map.singleton (ifDeclName ifd) ifd
      | decl <- concatMap T.groupDecls dgs
      , let ifd = T.mkIfaceDecl decl
      ]

-- |
-- Module      :  Cryptol.ModuleSystem.Env
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.ModuleSystem.Env where

#ifndef RELOCATABLE
import Paths_cryptol (getDataDir)
#endif

import Cryptol.Eval (EvalEnv)
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name (Supply,emptySupply)
import qualified Cryptol.ModuleSystem.NamingEnv as R
import Cryptol.Parser.AST
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP (PP(..),text,parens,NameDisp)

import Data.ByteString(ByteString)
import Control.Monad (guard,mplus)
import qualified Control.Exception as X
import Data.Function (on)
import qualified Data.Map as Map
import Data.Maybe(fromMaybe)
import Data.Semigroup
import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import System.Environment(getExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, takeDirectory)
import qualified Data.List as List

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

-- Module Environment ----------------------------------------------------------

-- | This is the current state of the interpreter.
data ModuleEnv = ModuleEnv
  { meLoadedModules :: LoadedModules
    -- ^ Information about all loaded modules.  See 'LoadedModule'.
    -- Contains information such as the file where the module was loaded
    -- from, as well as the module's interface, used for type checking.

  , meNameSeeds     :: T.NameSeeds
    -- ^ A source of new names for the type checker.

  , meSolverConfig  :: T.SolverConfig
    -- ^ Configuration settings for the SMT solver used for type-checking.

  , meEvalEnv       :: EvalEnv
    -- ^ The evaluation environment.  Contains the values for all loaded
    -- modules, both public and private.

  , meCoreLint      :: CoreLint
    -- ^ Should we run the linter to ensure sanity.

  , meMonoBinds     :: !Bool
    -- ^ Are we assuming that local bindings are monomorphic.
    -- XXX: We should probably remove this flag, and set it to 'True'.



  , meFocusedModule :: Maybe ModName
    -- ^ The "current" module.  Used to decide how to print names, for example.

  , meSearchPath    :: [FilePath]
    -- ^ Where we look for things.

  , meDynEnv        :: DynamicEnv
    -- ^ This contains additional definitions that were made at the command
    -- line, and so they don't reside in any module.

  , meSupply        :: !Supply
    -- ^ Name source for the renamer

  } deriving Generic

instance NFData ModuleEnv

-- | Should we run the linter?
data CoreLint = NoCoreLint        -- ^ Don't run core lint
              | CoreLint          -- ^ Run core lint
  deriving (Generic, NFData)

resetModuleEnv :: ModuleEnv -> ModuleEnv
resetModuleEnv env = env
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
    { meLoadedModules = mempty
    , meNameSeeds     = T.nameSeeds
    , meEvalEnv       = mempty
    , meFocusedModule = Nothing
      -- we search these in order, taking the first match
    , meSearchPath    = searchPath
    , meDynEnv        = mempty
    , meMonoBinds     = True
    , meSolverConfig  = T.SolverConfig
                          { T.solverPath = "z3"
                          , T.solverArgs = [ "-smt2", "-in" ]
                          , T.solverVerbose = 0
                          , T.solverPreludePath = searchPath
                          }
    , meCoreLint      = NoCoreLint
    , meSupply        = emptySupply
    }

-- | Try to focus a loaded module in the module environment.
focusModule :: ModName -> ModuleEnv -> Maybe ModuleEnv
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

-- | Are any parameterized modules loaded?
hasParamModules :: ModuleEnv -> Bool
hasParamModules = not . null . lmLoadedParamModules . meLoadedModules


-- | Produce an ifaceDecls that represents the focused environment of the module
-- system, as well as a 'NameDisp' for pretty-printing names according to the
-- imports.
--
-- XXX This could really do with some better error handling, just returning
-- mempty when one of the imports fails isn't really desirable.
--
-- XXX: This is not quite right.   For example, it does not take into
-- account *how* things were imported in a module (e.g., qualified).
-- It would be simpler to simply store the naming environment that was
-- actually used when we renamed the module.
focusedEnv :: ModuleEnv -> (IfaceParams,IfaceDecls,R.NamingEnv,NameDisp)
focusedEnv me =
  fromMaybe (noIfaceParams, mempty, mempty, mempty) $
  do fm   <- meFocusedModule me
     lm   <- lookupModule fm me
     deps <- mapM loadImport (T.mImports (lmModule lm))
     let (ifaces,names) = unzip deps
         Iface { .. }   = lmInterface lm
         localDecls     = ifPublic `mappend` ifPrivate
         localNames     = R.unqualifiedEnv localDecls `mappend`
                                              R.modParamsNamingEnv ifParams
         namingEnv      = localNames `R.shadowing` mconcat names

     return ( ifParams
            , mconcat (localDecls:ifaces)
            , namingEnv
            , R.toNameDisp namingEnv)
  where
  loadImport imp =
    do lm <- lookupModule (iModule imp) me
       let decls = ifPublic (lmInterface lm)
       return (decls,R.interpImport imp decls)

-- | The unqualified declarations and name environment for the dynamic
-- environment.
dynamicEnv :: ModuleEnv -> (IfaceDecls,R.NamingEnv,NameDisp)
dynamicEnv me = (decls,names,R.toNameDisp names)
  where
  decls = deIfaceDecls (meDynEnv me)
  names = R.unqualifiedEnv decls


-- Loaded Modules --------------------------------------------------------------

-- | The location of a module
data ModulePath = InFile FilePath
                | InMem String ByteString -- ^ Label, content
    deriving (Show, Generic, NFData)

-- | In-memory things are compared by label.
instance Eq ModulePath where
  p1 == p2 =
    case (p1,p2) of
      (InFile x, InFile y) -> x == y
      (InMem a _, InMem b _) -> a == b
      _ -> False

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

  } deriving (Show, Generic, NFData)

getLoadedModules :: LoadedModules -> [LoadedModule]
getLoadedModules x = lmLoadedParamModules x ++ lmLoadedModules x

instance Semigroup LoadedModules where
  l <> r = LoadedModules
    { lmLoadedModules = List.unionBy ((==) `on` lmName)
                                      (lmLoadedModules l) (lmLoadedModules r)
    , lmLoadedParamModules = lmLoadedParamModules l ++ lmLoadedParamModules r }

instance Monoid LoadedModules where
  mempty = LoadedModules { lmLoadedModules = []
                         , lmLoadedParamModules = []
                         }
  mappend l r = l <> r

data LoadedModule = LoadedModule
  { lmName              :: ModName
  , lmFilePath          :: ModulePath
    -- ^ The file path used to load this module (may not be canonical)
  , lmModuleId          :: String
    -- ^ An identifier used to identify the source of the bytes for the module.
    -- For files we just use the cononical path, for in memory things we
    -- use their label.
  , lmInterface         :: Iface
  , lmModule            :: T.Module
  , lmFingerprint       :: Fingerprint
  } deriving (Show, Generic, NFData)

-- | Has this module been loaded already.
isLoaded :: ModName -> LoadedModules -> Bool
isLoaded mn lm = any ((mn ==) . lmName) (getLoadedModules lm)

-- | Is this a loaded parameterized module.
isLoadedParamMod :: ModName -> LoadedModules -> Bool
isLoadedParamMod mn ln = any ((mn ==) . lmName) (lmLoadedParamModules ln)

-- | Try to find a previously loaded module
lookupModule :: ModName -> ModuleEnv -> Maybe LoadedModule
lookupModule mn me = search lmLoadedModules `mplus` search lmLoadedParamModules
  where
  search how = List.find ((mn ==) . lmName) (how (meLoadedModules me))


-- | Add a freshly loaded module.  If it was previously loaded, then
-- the new version is ignored.
addLoadedModule ::
  ModulePath -> String -> Fingerprint -> T.Module -> LoadedModules -> LoadedModules
addLoadedModule path ident fp tm lm
  | isLoaded (T.mName tm) lm  = lm
  | T.isParametrizedModule tm = lm { lmLoadedParamModules = loaded :
                                                lmLoadedParamModules lm }
  | otherwise                = lm { lmLoadedModules =
                                          lmLoadedModules lm ++ [loaded] }
  where
  loaded = LoadedModule
    { lmName            = T.mName tm
    , lmFilePath        = path
    , lmModuleId        = ident
    , lmInterface       = genIface tm
    , lmModule          = tm
    , lmFingerprint     = fp
    }

-- | Remove a previously loaded module.
removeLoadedModule :: (LoadedModule -> Bool) -> LoadedModules -> LoadedModules
removeLoadedModule rm lm =
  LoadedModules
    { lmLoadedModules = filter (not . rm) (lmLoadedModules lm)
    , lmLoadedParamModules = filter (not . rm) (lmLoadedParamModules lm)
    }


-- Dynamic Environments --------------------------------------------------------

-- | Extra information we need to carry around to dynamically extend
-- an environment outside the context of a single module. Particularly
-- useful when dealing with interactive declarations as in @:let@ or
-- @it@.

data DynamicEnv = DEnv
  { deNames :: R.NamingEnv
  , deDecls :: [T.DeclGroup]
  , deEnv   :: EvalEnv
  } deriving (Generic, NFData)

instance Semigroup DynamicEnv where
  de1 <> de2 = DEnv
    { deNames = deNames de1 <> deNames de2
    , deDecls = deDecls de1 <> deDecls de2
    , deEnv   = deEnv   de1 <> deEnv   de2
    }

instance Monoid DynamicEnv where
  mempty = DEnv
    { deNames = mempty
    , deDecls = mempty
    , deEnv   = mempty
    }
  mappend de1 de2 = de1 <> de2

-- | Build 'IfaceDecls' that correspond to all of the bindings in the
-- dynamic environment.
--
-- XXX: if we ever add type synonyms or newtypes at the REPL, revisit
-- this.
deIfaceDecls :: DynamicEnv -> IfaceDecls
deIfaceDecls DEnv { deDecls = dgs } =
  mconcat [ IfaceDecls
            { ifTySyns   = Map.empty
            , ifNewtypes = Map.empty
            , ifAbstractTypes = Map.empty
            , ifDecls    = Map.singleton (ifDeclName ifd) ifd
            }
          | decl <- concatMap T.groupDecls dgs
          , let ifd = mkIfaceDecl decl
          ]

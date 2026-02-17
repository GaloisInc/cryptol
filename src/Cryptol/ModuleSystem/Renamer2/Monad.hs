{-# Language BlockArguments, BangPatterns, ImportQualifiedPost #-}
{-# Language GeneralisedNewtypeDeriving #-}
module Cryptol.ModuleSystem.Renamer2.Monad
  ( 
    -- * Renamer monad
    RenameM
  , runRenamer
  , RenamerInfo(..)

    -- * Modules
  , lookupMod
  , addResolvedMod
  , recordTopImport
  , getExternalDeps
  , Mod(..)

    -- * The current module
  , getCurModPath
  , getCurDefs
  , getCurScope
  , setThisModuleDefs
  , addImported
  , addLocals
  , inSubmodule

    -- * Name generation
  , withSupply

    -- * Error reporting
  , recordError
  , quit
  , getCurLoc
  , located
  , withLoc
  , reportUnboundName
  , mkFakeName
  ) where

import MonadLib
import Data.Set(Set)
import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map

import Cryptol.Utils.Panic
import Cryptol.Utils.Ident
import Cryptol.Parser.Name
import Cryptol.Parser.Position
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Binds hiding (Mod(..), ifaceToMod, modToMap, ifaceSigToMod)
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Exports
import Cryptol.TypeCheck.Type(ModParamNames)


newtype RenameM a = R (ReaderT RO (ExceptionT () (StateT RW Lift)) a)
  deriving (Functor,Applicative,Monad)

-- | Information needed to do some renaming.
data RenamerInfo = RenamerInfo
  { renSupply   :: Supply     -- ^ Use to make new names
  , renContext  :: ModPath    -- ^ We are renaming things in here
  , renEnv      :: NamingEnv  -- ^ This is what's in scope
  , renIfaces   :: Map ModName (Either ModParamNames Iface)
    -- ^ External modules. These include normal modules, and functors
    -- (on the Right), as well as interfaces (on the Left)
  }


-- | Do some renaming.
runRenamer ::
  RenamerInfo ->
  RenameM a ->
  (Either [RenamerError] (a,Supply), [RenamerWarning])
runRenamer info (R m) = (res, renWarnings rwFin)
    where
    (mres, rwFin) = runLift (runStateT rw0 (runExceptionT (runReaderT ro0 m)))
    res =
      case mres of
        Left () -> Left (renErrors rwFin)
        Right a -> Right (a, newNames rwFin)

    ro0 = RO {
      curModPath = renContext info,
      curLoc = emptyRange, -- XXX?
      loadedIfaces =
        let hasIf x =
              case x of
                Left {} -> Nothing
                Right i -> Just i
        in Map.mapMaybe hasIf (renIfaces info)
    }

    rw0 = RW {
      localsEnv = mempty,
      defEnv = mempty,
      impEnv = mempty,
      outEnv = mempty,
      externalDeps = mempty,
      newNames = renSupply info,
      renErrors = [],
      renWarnings = [],
      knownMods =
        Map.unions [  
          case ent of
            Left ps -> Map.singleton (ImpTop t) (ifaceSigToMod ps)
            Right i -> ifaceToMod (ImpTop t) i
          | (t,ent) <- Map.toList (renIfaces info)
        ]

    }


data RO = RO {
  curModPath :: ModPath,
  -- ^ Current module that we are working on

  curLoc :: Range,
  -- ^ The source location where we are doing something

  loadedIfaces :: Map ModName Iface
  -- ^ Interfaces for external loaded modules.
  -- We keep this so then if one of the modules is imported, we can
  -- collect its definitions in `externalDeps` to give the typechecker.
}

data RW = RW {

  knownMods :: ModMap,
  -- ^ Information about previously processed modules

  externalDeps :: IfaceDecls,
  -- ^ Interface declarations for imported external modules.
  -- We track this so we can give it to the type checker.
  
  localsEnv :: NamingEnv,
  -- ^ Variables local to a function.

  defEnv :: NamingEnv,
  -- ^ Things defined in the current module

  impEnv :: NamingEnv,
  -- ^ Things imported in the current scope

  outEnv :: NamingEnv,
  -- ^ Things defined in an enclosing scope (for nested modules)

  newNames :: !Supply,
  -- ^ Used to generate unique names when renaming

  renErrors :: [RenamerError],
  -- ^ Errors we found

  renWarnings :: [RenamerWarning]
  -- ^ Warnings we'd like to emit.
}

--------------------------------------------------------------------------------
-- Module Manipulation
--------------------------------------------------------------------------------


-- | Information about a processed module.
data Mod = Mod
  { modKind      :: ModKind             -- ^ What sort of thing are we
  , modDefines   :: NamingEnv           -- ^ Things defined by this module.
  , modPublic    :: !(Set Name)         -- ^ These are the exported names
  }

lookupMod :: ImpName Name -> RenameM Mod
lookupMod nm =
  do
    rw <- R get
    case Map.lookup nm (knownMods rw) of
      Just mo -> pure mo
      Nothing -> panic "lookupMod" ["Missing module"]

recordTopImport :: ModName -> RenameM ()
recordTopImport m =
  do
    ro <- R ask
    case Map.lookup m (loadedIfaces ro) of
      Just ifa ->
        R (sets_ \rw -> rw { externalDeps = ifDefines ifa <> externalDeps rw })
      Nothing -> panic "recordTopImport" ["Missing module"]

getExternalDeps :: RenameM IfaceDecls
getExternalDeps = R (externalDeps <$> get)

type ModMap = Map (ImpName Name) Mod

-- | Make a `Mod` from the public declarations in a top-level module's interface.
-- This is used to handle imports.
ifaceToMod :: ImpName Name -> IfaceG name -> ModMap
ifaceToMod nm iface =
  ifaceNamesToMod iface (ifaceIsFunctor iface) nm (ifNames iface)

-- | Generate a module or functor from the given names.
ifaceNamesToMod ::
    IfaceG topname -> Bool -> ImpName Name -> IfaceNames name -> ModMap
ifaceNamesToMod iface params nm names =
  Map.unions (Map.fromList ((nm,mo) : sigs) : funs ++ nest)
  where
  sigs =
    [ (ImpNested k, ifaceSigToMod v) | (k,v) <- Map.toList (ifSignatures decls) ]
  funs =
    [ ifaceToMod (ImpNested k) v | (k,v) <- Map.toList (ifFunctors decls) ]
  nest =
    [ ifaceNamesToMod iface False (ImpNested k) v
    | (k,v) <- Map.toList (ifModules decls) ]
  mo = Mod
    { modKind    = if params then AFunctor else AModule
    , modDefines = namingEnvFromNames defs
    , modPublic  = ifsPublic names
    }
  defs      = ifsDefines names
  isLocal x = x `Set.member` defs
  decls     = filterIfaceDecls isLocal (ifDefines iface)

-- | Generate a module corresponding to an interface module.
ifaceSigToMod :: ModParamNames -> Mod
ifaceSigToMod ps = Mod
  { modKind      = ASignature
  , modDefines   = env
  , modPublic    = namingEnvNames env
  }
  where
  env = modParamNamesNamingEnv ps

addResolvedMod :: ModuleG Name Name -> RenameM ()
addResolvedMod mo =
  do
    env <- getCurDefs
    let nm = ImpNested (thing (mName mo))
    summary <-
      case mDef mo of
        NormalModule ds ->
          pure Mod {
              modKind = if any isParamDecl ds
                            then AFunctor else AModule,
              modDefines = env,
              modPublic = Set.unions (map (`exported` expSpec) allNamespaces)
            }
          where expSpec = exportedDecls ds
            
        FunctorInstance f _ inst ->
          do
            fmo <- lookupMod (thing f)
            let remap x = case Map.lookup x inst of
                            Just y -> y
                            Nothing -> panic "addResolvedMod" ["remap failed"]
            pure Mod {
              modKind = AModule,
              modDefines = env,
                -- NOTE: XXX: revisit, if curDefs is not defined we can get
                -- this from fmo
              modPublic = Set.map remap (modPublic fmo)
            }
              
        InterfaceModule {} ->
          pure Mod {
            modKind = ASignature,
            modDefines = env,
            modPublic = namingEnvNames env
          }
    R (sets_ \rw -> rw { knownMods = Map.insert nm summary (knownMods rw) })



--------------------------------------------------------------------------------
-- The current module
--------------------------------------------------------------------------------

-- | What module we are currently processing.
getCurModPath :: RenameM ModPath
getCurModPath = R (curModPath <$> ask)

-- | Get just the things defined in the current module
getCurDefs :: RenameM NamingEnv
getCurDefs = R (defEnv <$> get)

-- | Compute the current scope, including local definitions, outer environment
-- and imports.
getCurScope :: RenameM NamingEnv
getCurScope = R
  do
    rw <- get
    pure $
      localsEnv rw `shadowing`
      defEnv    rw `shadowing`
      impEnv    rw `shadowing`
      outEnv    rw

-- | Set the definition for the current module.
setThisModuleDefs :: NamingEnv -> RenameM ()
setThisModuleDefs env = R (sets_ \rw -> rw { defEnv = env })

-- | Add some names that came from an import.
addImported :: NamingEnv -> RenameM ()
addImported env = R (sets_ \rw -> rw { impEnv = env <> impEnv rw })
-- XXX: Warn about shadowing

addLocals :: NamingEnv -> RenameM ()
addLocals env = R (sets_ \rw -> rw { localsEnv = env <> localsEnv rw })
-- XXX: Warn about shadowing

-- | Do some renaming in the context of a nested module.
inSubmodule :: Ident -> RenameM a -> RenameM a
inSubmodule x (R m) = R
  do
    let upd ro = ro { curModPath = Nested (curModPath ro) x }
    rw <- get
    let defs = defEnv rw
        imps = impEnv rw
        outs = outEnv rw
        -- there should be no locals
    set rw {
      defEnv     = mempty,
      impEnv     = mempty,
      outEnv     = defs `shadowing` imps `shadowing` outs
      }
    a <- mapReader upd m
    sets_ \rw1 -> rw1 { defEnv = defs, impEnv = imps, outEnv = outs } 
    pure a


--------------------------------------------------------------------------------
-- Name generation
--------------------------------------------------------------------------------

-- | Do something that require name generation.
withSupply :: (Supply -> (a,Supply)) -> RenameM a
withSupply f = R (sets \rw ->
  case f (newNames rw) of
    (a,s1) -> (a, rw1)
      where !rw1 = rw { newNames = s1 })


--------------------------------------------------------------------------------
-- Error reporting
--------------------------------------------------------------------------------

recordError :: RenamerError -> RenameM ()
recordError e = R (sets_ \rw -> rw { renErrors = e : renErrors rw })

quit :: RenameM a
quit = R (raise ())

getCurLoc :: RenameM Range
getCurLoc = R (curLoc <$> ask)

-- | Annotate something with the current range.
located :: a -> RenameM (Located a)
located a =
  do loc <- getCurLoc
     return Located { thing = a, srcRange = loc }

withLoc :: HasLoc loc => loc -> RenameM a -> RenameM a
withLoc th (R m) = R
  case getLoc th of
    Nothing -> m
    Just r -> mapReader (\ro -> ro { curLoc = r }) m

-- | Generate an error for a name that we cannot resolve.
-- We try to give a hint, if the name appears in a different name space.
reportUnboundName :: Namespace -> PName -> NamingEnv -> RenameM Name
reportUnboundName expected qn scope =
  do 
     let others     = [ ns | ns <- allNamespaces
                           , ns /= expected
                           , Just _ <- [lookupNS ns qn scope] ]
                         
     nm <- located qn
     case others of
       -- name exists in a different namespace
       actual : _ -> recordError (WrongNamespace expected actual nm)

       -- the value is just missing
       [] -> recordError (UnboundName expected nm)

     mkFakeName expected qn

-- | Assuming an error has been recorded already, construct a fake name that's
-- not expected to make it out of the renamer.
mkFakeName :: Namespace -> PName -> RenameM Name
mkFakeName ns pn =
  do loc <- getCurLoc
     withSupply (mkDeclared ns (TopModule undefinedModName)
                               SystemName (getIdent pn) Nothing loc)


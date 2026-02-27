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
  , addInstMod
  , recordTopImport
  , getExternalDeps
  , Mod(..)

    -- * The current module
  , getCurModPath
  , getCurTopDefs
  , getCurBinds
  , getCurScope
  , setThisModuleDefs
  , addModParams
  , addImported

    -- * Scopes
  , inSubmodule
  , inLocalScope
  , inLocalBindScope
  , doBind
  , getLastBindDefs

    -- * Name generation
  , doDefGroup
  , doDefOrdGroup

    -- * Error reporting
  , recordError
  , addWarning
  , quit
  , getCurLoc
  , located
  , withLoc
  , reportUnboundName

    -- * Dependency tracking
  , recordNameUses
  , getDeps
  ) where

-- import Debug.Trace
-- import Cryptol.Utils.PP

import MonadLib
import Data.Maybe(fromMaybe,maybeToList)
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
runRenamer info (R m) = (res, reverse (renWarnings rwFin))
    where
    (mres, rwFin) = runLift (runStateT rw0 (runExceptionT (runReaderT ro0 m)))
    res =
      case renErrors rwFin of
        [] | Right a <- mres -> Right (a, newNames rwFin)
        es -> Left (reverse es)

    ro0 = RO {
      lastBindsEnv = mempty,
      localsEnv = mempty,
      localBindEnv = mempty,
      outEnv = renEnv info,
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
      defEnv = mempty,
      impEnv = mempty,
      modParamEnv = mempty,
      modParamNames = mempty,
      externalDeps = mempty,
      newNames = renSupply info,
      renErrors = [],
      renWarnings = [],
      usedNames = Set.empty,
      knownMods =
        Map.unions [  
          case ent of
            Left ps -> Map.singleton (ImpTop t) (ModKnown (ifaceSigToMod ps))
            Right i -> ifaceToMod (ImpTop t) i
          | (t,ent) <- Map.toList (renIfaces info)
        ]

    }


data RO = RO {
  curModPath :: ModPath,
  -- ^ Current module that we are working on

  curLoc :: Range,
  -- ^ The source location where we are doing something

  loadedIfaces :: Map ModName Iface,
  -- ^ Interfaces for external loaded modules.
  -- We keep this so then if one of the modules is imported, we can
  -- collect its definitions in `externalDeps` to give the typechecker.

  lastBindsEnv :: NamingEnv,
  -- ^ This is the last environment that introduced function bindings.
  -- It is basically the value of `getCurBinds` at the point we start
  -- resolving a binding.  We need this, because during `NoPat`, we desugar
  -- bindings with arguments, into lambdas, but those lambdas are annotated
  -- with the name of the function that gave rice to them.  We use this
  -- environment to avoid resolve this name, thus avoiding confusion with
  -- the parameters of the function.

  localBindEnv :: NamingEnv,
  -- ^ Used to resolve the names of definitions in the current scope.

  localsEnv :: NamingEnv,
  -- ^ Variables local to a function. These are variables from outside the
  -- current binding scope.

  outEnv :: NamingEnv
  -- ^ Things defined in an enclosing scope (for nested modules)
}

data RW = RW {

  knownMods :: ModMap,
  -- ^ Information about previously processed modules

  externalDeps :: IfaceDecls,
  -- ^ Interface declarations for imported external modules.
  -- We track this so we can give it to the type checker.
  
  defEnv :: NamingEnv,
  -- ^ Things defined in the current module

  modParamEnv :: NamingEnv,
  -- ^ Names from module parameters

  modParamNames :: Map Ident Range,
  -- ^ Names of module parameters for the current module

  impEnv :: NamingEnv,
  -- ^ Things imported in the current scope

  newNames :: !Supply,
  -- ^ Used to generate unique names when renaming

  renErrors :: [RenamerError],
  -- ^ Errors we found

  renWarnings :: [RenamerWarning],
  -- ^ Warnings we'd like to emit.

  usedNames :: Set Name
  -- ^ Every time we resove a name use we record it here.
  -- In this way we can determine the dependencies of things.
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

-- | A dummy module to use as placeholder for error situations
emptyMod :: ModKind -> Mod
emptyMod k = Mod {
  modKind = k,
  modDefines = mempty,
  modPublic = mempty
}


-- | Lookup a known module
lookupMod :: ImpName Name -> Maybe ModKind -> RenameM Mod
lookupMod nm mbExpected =
  do
    rw <- R get
    case Map.lookup nm (knownMods rw) of
      Just (ModKnown mo) ->
        case mbExpected of
          Nothing -> pure mo
          Just expected
            | expected == actual -> pure mo
            | otherwise ->
              do
                loc <- getCurLoc
                recordError (ModuleKindMismatch loc nm expected actual)
                pure (emptyMod expected)
              where actual = modKind mo
      Just ModTodo ->
        do
          loc <- getCurLoc
          case nm of
            ImpNested x ->
              recordError (ImportTooSoon loc (nameIdent x))
            ImpTop {} -> panic "lookupMod" ["ModTodo"]
          pure (emptyMod (fromMaybe AModule mbExpected))
      Just ModFake ->
          pure (emptyMod (fromMaybe AModule mbExpected))

      Nothing ->
        panic "lookupMod" ["Resolved name, but unknown module"]

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

data ModStatus = ModKnown Mod | ModFake | ModTodo

type ModMap = Map (ImpName Name) ModStatus

-- | Make a `Mod` from the public declarations in a top-level module's interface.
-- This is used to handle imports.
ifaceToMod :: ImpName Name -> IfaceG name -> ModMap
ifaceToMod nm iface =
  ifaceNamesToMod iface (ifaceIsFunctor iface) nm (ifNames iface)

-- | Generate a module or functor from the given names.
ifaceNamesToMod ::
    IfaceG topname -> Bool -> ImpName Name -> IfaceNames name -> ModMap
ifaceNamesToMod iface params nm names =
  Map.unions (Map.fromList ((nm,ModKnown mo) : sigs) : funs ++ nest)
  where
  sigs =
    [ (ImpNested k, ModKnown (ifaceSigToMod v)) | (k,v) <- Map.toList (ifSignatures decls) ]
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

-- | Add a module that was generated when instantiating a functor
addInstMod :: Name -> Mod -> RenameM ()
addInstMod x y =
  R (sets_ \rw -> rw { knownMods = Map.insert (ImpNested x) (ModKnown y) (knownMods rw) })

addResolvedMod :: NamingEnv -> ModuleG Name Name -> RenameM ()
addResolvedMod env mo =
  do
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
            fmo <- withLoc (srcRange f) (lookupMod (thing f) (Just AFunctor))
            let remap x = case Map.lookup x inst of
                            Just y -> y
                            Nothing -> panic "addResolvedMod" ["remap failed"]
            pure Mod {
              modKind = AModule,
              modDefines = env,
              modPublic = Set.map remap (modPublic fmo)
            }
              
        InterfaceModule {} ->
          pure Mod {
            modKind = ASignature,
            modDefines = env,
            modPublic = namingEnvNames env
          }
    R (sets_ \rw -> rw { knownMods = Map.insert nm (ModKnown summary) (knownMods rw) })



--------------------------------------------------------------------------------
-- The current module
--------------------------------------------------------------------------------

-- | What module we are currently processing.
getCurModPath :: RenameM ModPath
getCurModPath = R (curModPath <$> ask)

-- | Get just the things defined in the current module
getCurTopDefs :: RenameM NamingEnv
getCurTopDefs = R (defEnv <$> get)

-- | Get things defined in the current module, and any local bindings in scope.
-- Used for resolving name definitions
getCurBinds :: RenameM NamingEnv
getCurBinds = R
  do
    ro <- ask
    rw <- get
    pure (localBindEnv ro <> defEnv rw)


-- | Compute the current scope, including local definitions, outer environment
-- and imports.
getCurScope :: RenameM NamingEnv
getCurScope = R
  do
    ro <- ask
    rw <- get
    pure $
      localsEnv ro `shadowing`
      localBindEnv ro `shadowing`
      defEnv    rw `shadowing`
      modParamEnv rw `shadowing`
      impEnv    rw `shadowing`
      outEnv    ro

-- | Set the definition for the current module.
setThisModuleDefs :: NamingEnv -> RenameM ()
setThisModuleDefs env =
  R (sets_ \rw -> rw { defEnv = env,
                       knownMods = todoMods `Map.union` knownMods rw
                     })
  where
  todoMods =
    Map.fromList 
      [ (ImpNested x,ModTodo)
      | x <- Set.toList (namingEnvNames env), nameNamespace x == NSModule
      ]

-- | Add names from module parameters to the current scope.
-- It is an error if the module parameters conflict with the
-- definitions in a module.
addModParams :: Located Ident -> NamingEnv -> RenameM ()
addModParams nm env =
  do
    errs <- R (sets upd)
    mapM_ recordError errs
    when (not (null errs)) quit
  where
  upd rw =
    let nms    = modParamNames rw
        newEnv = env <> modParamEnv rw
        errs   =
          [ MultipleModParams (thing nm) [r,srcRange nm]
          | r <- maybeToList (Map.lookup (thing nm) nms) ] ++
          map OverlappingSyms (findAmbig newEnv)
    in (errs, rw {
                modParamEnv = newEnv,
                modParamNames = Map.insert (thing nm) (srcRange nm) nms })

-- | Add some names that came from an import.
addImported :: NamingEnv -> RenameM ()
addImported env = R (sets_ \rw -> rw { impEnv = env <> impEnv rw })
-- XXX: Warn about shadowing

-- | Capture the `getCurBinds` at this point.  See the comment
-- on `lastBindsEnv` for more info.
doBind :: RenameM a -> RenameM a
doBind (R m) =
  do
    env <- getCurBinds
    R (mapReader (\ro -> ro { lastBindsEnv = env }) m)

getLastBindDefs :: RenameM NamingEnv
getLastBindDefs = R (lastBindsEnv <$> ask)

-- | Set the names of bindings for the duration of a computation.
-- XXX: Shadowing
inLocalBindScope :: NamingEnv -> RenameM a -> RenameM a
inLocalBindScope env (R m) = R (mapReader upd m)
  where
  upd ro = ro {
    localBindEnv = env,
    localsEnv = localBindEnv ro `shadowing` localsEnv ro
  }


-- | Do something that will only modify the local scope, and restore
-- it after the computation.  Usually we use `inLocalBindScope`, but
-- we use this for list comprehensions, because the binders in the arms
-- need to be combined when processing the "head" of the comprehension.
-- XXX: Shadowing
inLocalScope :: NamingEnv -> RenameM a -> RenameM a
inLocalScope env (R m) = R (mapReader upd m)
  where
  upd ro = ro {
    localsEnv = env `shadowing` localsEnv ro
  }

    

-- | Do some renaming in the context of a nested module.
inSubmodule :: Ident -> RenameM a -> RenameM a
inSubmodule x (R m) =
  do
    rw <- R get
    let defs = defEnv rw
        pars = modParamEnv rw
        parns = modParamNames rw
        imps = impEnv rw
        
    let upd ro = ro {
          curModPath = Nested (curModPath ro) x,
          outEnv     = defs `shadowing` pars `shadowing` imps `shadowing` outEnv ro
        }

    R $ set rw {
      defEnv      = mempty,
      impEnv      = mempty,
      modParamEnv = mempty,
      modParamNames = mempty
    }
    a <- mapReader upd m
    sets_ \rw1 -> 
      let bound = Set.unions
                    (map namingEnvNames
                      [ defEnv rw1, impEnv rw1, modParamEnv rw1 ])
      in
      rw1 { defEnv = defs,
                        modParamEnv = pars,
                        impEnv      = imps,
                        usedNames   = usedNames rw1 `Set.difference` bound
                      } 
    pure a


--------------------------------------------------------------------------------
-- Error reporting
--------------------------------------------------------------------------------

recordError :: RenamerError -> RenameM ()
recordError e = R (sets_ \rw -> rw { renErrors = e : renErrors rw })

addWarning :: RenamerWarning -> RenameM ()
addWarning e = R (sets_ \rw -> rw { renWarnings = e : renWarnings rw })

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

    -- traceM ("UNDEFINED NAME IN " ++ show (pp expected) ++ ": " ++ show (pp qn) ++ "\n" ++ show (pp scope))

    mkFakeName expected qn


--------------------------------------------------------------------------------
-- Name generation
--------------------------------------------------------------------------------

instance FreshM RenameM where
  liftSupply f =
    R (sets \rw ->
      case f (newNames rw) of
        (a,s1) -> (a, rw1)
          where !rw1 = rw { newNames = s1 })

-- | Make names for a bunch of things defined together.
-- Check that they all have distinct names.
-- We also return the names defined by each entry.
-- This is useful for when we need to rearrange the entries in dependency
-- order.
doDefOrdGroup :: BindsNames a => [a] -> RenameM (NamingEnv,[Set Name])
doDefOrdGroup as =
  do
    envs <- mapM (liftSupply . defsOf) as
    let env = mconcat envs
        errs = findAmbig env
    mapM_ (recordError . OverlappingSyms) errs
    when (not (null errs)) quit
    pure (env, map namingEnvNames envs)


-- | Make names for a bunch of things defined together.
-- Check that they all have distinct names.
doDefGroup :: (Supply -> (NamingEnv, Supply)) -> RenameM NamingEnv
doDefGroup m =
  do
    env <- liftSupply m
    let errs = findAmbig env
    mapM_ (recordError . OverlappingSyms) (findAmbig env)
    when (not (null errs)) quit
    pure env

-- | Assuming an error has been recorded already, construct a fake name that's
-- not expected to make it out of the renamer.
mkFakeName :: Namespace -> PName -> RenameM Name
mkFakeName ns pn =
  do
    loc <- getCurLoc
    nm <-
      liftSupply (mkDeclared ns (TopModule undefinedModName)
                               SystemName (getIdent pn) Nothing loc)
    R (sets_ \rw -> rw { defEnv = singletonNS ns pn nm `shadowing` defEnv rw,
                         knownMods =
                          case ns of
                            NSModule -> Map.insert (ImpNested nm) ModFake (knownMods rw)
                            _ -> knownMods rw })
    pure nm 


--------------------------------------------------------------------------------
-- Dependency Tracking
--------------------------------------------------------------------------------

-- | Collect all names used while running the given computation.
-- Note that the names of the sub-computation are *NOT* added to the dependencies.
getDeps :: RenameM a -> RenameM (a, Set Name)
getDeps (R m) = R
  do
    curUses <- sets \rw -> (usedNames rw, rw { usedNames = Set.empty })
    a <- m
    sets \rw -> ((a,usedNames rw), rw { usedNames = usedNames rw <> curUses })

-- | Add some dependencies for the current thing we are working on.
recordNameUses :: Set Name -> RenameM ()
recordNameUses xs =
  R (sets_ \rw -> rw { usedNames = Set.union xs (usedNames rw) })
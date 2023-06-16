{- |

This module deals with imports of nested modules (@import submodule@).
This is more complex than it might seem at first because to resolve a
declaration like @import submodule X@ we need to resolve what @X@
referes to before we know what it will import.

Even triciker is the case for functor instantiations:

  module M = F { X }
  import M

In this case, even if we know what `M` referes to, we first need to
resolve `F`, so that we can generate the instantiation and generate
fresh names for names defined by `M`.

If we want to support applicative semantics, then before instantiation
`M` we also need to resolve `X` so that we know if this instantiation has
already been generated.

An overall guiding principle of the design is that we assume that declarations
can be ordered in dependency order, and submodules can be processed one
at a time. In particular, this does not allow recursion across modules,
or functor instantiations depending on their arguments.

Thus, the following is OK:

module A where
  x = 0x2

  submodule B where
    y = x

  z = B::y


However, this is not OK:

  submodule A = F X
  submodule F where
    import A
-}

{-# Language BlockArguments #-}
{-# Language TypeSynonymInstances, FlexibleInstances #-}
module Cryptol.ModuleSystem.Renamer.Imports
  ( resolveImports
  , ResolvedModule(..)
  , ModKind(..)
  , ResolvedLocal
  , ResolvedExt
  )
  where

import Data.Maybe(fromMaybe)
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List(foldl')
import Control.Monad(when)
import qualified MonadLib as M

import Cryptol.Utils.PP(pp)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(ModName,ModPath(..),Namespace(..),OrigName(..))

import Cryptol.Parser.AST
  ( ImportG(..),PName, ModuleInstanceArgs(..), ImpName(..) )
import Cryptol.ModuleSystem.Binds (Mod(..), TopDef(..), modNested, ModKind(..))
import Cryptol.ModuleSystem.Name
          ( Name, Supply, SupplyT, runSupplyT, liftSupply, freshNameFor
          , asOrigName, nameIdent, nameTopModule )
import Cryptol.ModuleSystem.Names(Names(..))
import Cryptol.ModuleSystem.NamingEnv
          ( NamingEnv(..), lookupNS, shadowing, travNamingEnv
          , interpImportEnv, zipByTextName, filterUNames )


{- | This represents a resolved module or signaure.
The type parameter helps us distinguish between two types of resolved modules:

  1. Resolved modules that are *inputs* to the algorithm (i.e., they are
     defined outside the current module).  For such modules the type
     parameter is @imps@ is ()

  2. Resolved modules that are *outputs* of the algorithm (i.e., they
     are defined within the current module).  For such modules the type
     parameter @imps@ contains the naming environment for things
     that came in through the import.

Note that signaures are never "imported", however we do need to keep them
here so that signatures in a functor are properly instantiated when
the functor is instantiated.
-}
data ResolvedModule imps = ResolvedModule
  { rmodDefines   :: NamingEnv    -- ^ Things defined by the module/signature.
  , rmodPublic    :: !(Set Name)  -- ^ Exported names
  , rmodKind      :: ModKind      -- ^ What sort of thing are we
  , rmodNested    :: Set Name     -- ^ Modules and signatures nested in this one
  , rmodImports   :: imps
    {- ^ Resolved imports. External modules need not specify this field,
    it is just part of the thing we compute for local modules. -}
  }


-- | A resolved module that's defined in (or is) the current top-level module
type ResolvedLocal = ResolvedModule NamingEnv

-- | A resolved module that's not defined in the current top-level module
type ResolvedExt   = ResolvedModule ()


resolveImports ::
  (ImpName Name -> Mod ()) ->
  TopDef ->
  Supply ->
  (Map (ImpName Name) ResolvedLocal, Supply)
resolveImports ext def su =
  case def of

    TopMod m mo ->
      do let cur  = todoModule mo
             newS = doModuleStep CurState
                                   { curMod = cur
                                   , curTop = m
                                   , externalModules = ext
                                   , doneModules = mempty
                                   , nameSupply = su
                                   , changes = False
                                   }


         case tryFinishCurMod cur newS of
           Just r  -> add m r newS
           Nothing -> add m r s1
              where (r,s1) = forceFinish newS

    TopInst m f as ->
      do let s = CurState
                   { curMod = ()
                   , curTop = m
                   , externalModules = ext
                   , doneModules = mempty
                   , nameSupply = su
                   , changes = False
                   }

         case tryInstanceMaybe s (ImpTop m) (f,as) of
           Just (r,newS) -> add m r newS
           Nothing -> (Map.singleton (ImpTop m) forceResolveInst, su)

  where
  toNest m = Map.fromList [ (ImpNested k, v) | (k,v) <- Map.toList m ]
  add m r s  = ( Map.insert (ImpTop m) r (toNest (doneModules s))
               , nameSupply s
               )




--------------------------------------------------------------------------------


-- | This keeps track of the current state of resolution of a module.
type Todo = Mod ModState

data ModState = ModState
  { modOuter        :: NamingEnv
    -- ^ Things which come in scope from outer modules

  , modImported     :: NamingEnv
    -- ^ Things which come in scope via imports.  These shadow outer names.
  }


-- | Initial state of a module that needs processing.
todoModule :: Mod () -> Todo
todoModule = fmap (const emptyModState)
  where
  emptyModState =
    ModState
      { modOuter    = mempty
      , modImported = mempty
      }

{- | A module is fully processed when we are done with all its:

  * submodule imports
  * instantiations
  * nested things (signatures and modules)
-}
isDone :: Todo -> Bool
isDone m = null     (modImports m)   &&
           Map.null (modInstances m) &&
           Map.null (modMods m)


-- | Finish up all unfinished modules as best as we can
forceFinish :: CurState -> (ResolvedLocal,CurState)
forceFinish s0 =
  let this  = curMod s0
      add k v s = s { doneModules = Map.insert k v (doneModules s) }
      s1        = foldl' (\s k -> add k forceResolveInst s) s0
                         (Map.keys (modInstances this))

      doNestMod s (k,m) =
        let (r,s') = forceFinish s { curMod = m }
        in add k r s'

  in ( forceResolveMod this
     , foldl' doNestMod s1 (Map.toList (modMods this))
     )


-- | A place-holder entry for instnatitations we couldn't resolve.
forceResolveInst :: ResolvedLocal
forceResolveInst =
  ResolvedModule
    { rmodDefines = mempty
    , rmodPublic  = mempty
    , rmodKind    = AModule
    , rmodNested  = Set.empty
    , rmodImports = mempty
    }

-- | Finish up unresolved modules as well as we can, in situations where
-- the program contains an error.
forceResolveMod :: Todo -> ResolvedLocal
forceResolveMod todo =
  ResolvedModule
    { rmodDefines   = modDefines todo
    , rmodPublic    = modPublic todo
    , rmodKind      = modKind todo
    , rmodNested    = Map.keysSet (modMods todo)
    , rmodImports   = modImported (modState todo)
    }





pushImport :: ImportG (ImpName PName) -> Todo -> Todo
pushImport i m = m { modImports = i : modImports m }

pushInst :: Name -> (ImpName PName, ModuleInstanceArgs PName) -> Todo -> Todo
pushInst k v m = m { modInstances = Map.insert k v (modInstances m) }

pushMod :: Name -> Todo -> Todo -> Todo
pushMod k v m = m { modMods = Map.insert k v (modMods m) }

updMS :: (ModState -> ModState) -> Todo -> Todo
updMS f m = m { modState = f (modState m) }
--------------------------------------------------------------------------------



externalMod :: Mod () -> ResolvedExt
externalMod m = ResolvedModule
  { rmodDefines  = modDefines m
  , rmodPublic   = modPublic m
  , rmodKind     = modKind m
  , rmodNested   = modNested m
  , rmodImports  = ()
  }

{- | This is used when we need to use a local resolved module as an input
     to another module. -}
forget :: ResolvedLocal -> ResolvedExt
forget r = r { rmodImports = () }

type CurState = CurState' Todo

data CurState' a = CurState
  { curMod      :: a
    -- ^ This is what needs to be done

  , curTop      :: !ModName
    {- ^ The top-level module we are working on.  This does not change
       throught the algorithm, it is just convenient to pass it here with 
       all the other stuff. -}

  , externalModules :: ImpName Name -> Mod ()
    -- ^ Modules defined outside the current top-level modules

  , doneModules :: Map Name ResolvedLocal
    {- ^ Nested modules/signatures in the current top-level modules.
         These may be either defined locally, or be the result of
         instantiating a functor.  Note that the functor itself may be
         either local or external.
    -}

  , nameSupply :: Supply
    -- ^ Use this to instantiate functors

  , changes :: Bool
    -- ^ True if something changed on the last iteration
  }

updCur :: CurState -> (Todo -> Todo) -> CurState
updCur m f = m { curMod = f (curMod m) }

updCurMS :: CurState -> (ModState -> ModState) -> CurState
updCurMS s f = updCur s (updMS f)

class HasCurScope a where
  curScope :: CurState' a -> NamingEnv

instance HasCurScope () where
  curScope _ = mempty

instance HasCurScope Todo where
  curScope s = modDefines m `shadowing` modImported ms `shadowing` modOuter ms
    where
    m   = curMod s
    ms  = modState m


-- | Keep applying a transformation while things are changing
doStep :: (CurState -> CurState) -> (CurState -> CurState)
doStep f s0 = go (changes s0) s0
  where
  go ch s = let s1 = f s { changes = False }
            in if changes s1
                then go True s1
                else s { changes = ch }

-- | Is this a known name for a module in the current scope?
knownPName :: HasCurScope a => CurState' a -> PName -> Maybe Name
knownPName s x =
  do ns <- lookupNS NSModule x (curScope s)
     case ns of
       One n    -> pure n
       {- NOTE: since we build up what's in scope incrementally,
          it is possible that this would eventually be ambiguous,
          which we'll detect during actual renaming. -}

       Ambig {} -> Nothing
       {- We treat ambiguous imports as undefined, which may lead to
          spurious "undefined X" errors.  To avoid this we should prioritize
          reporting "ambiguous X" errors. -}

-- | Is the module mentioned in this import known in the current scope?
knownImpName ::
  HasCurScope a => CurState' a -> ImpName PName -> Maybe (ImpName Name)
knownImpName s i =
  case i of
    ImpTop m    -> pure (ImpTop m)
    ImpNested m -> ImpNested <$> knownPName s m

-- | Is the module mentioned in the import already resolved?
knownModule ::
  HasCurScope a => CurState' a -> ImpName Name -> Maybe ResolvedExt
knownModule s x
  | root == curTop s =
    case x of
      ImpNested y -> forget <$> Map.lookup y (doneModules s)
      ImpTop {}   -> Nothing   -- or panic? recursive import

  | otherwise = Just (externalMod (externalModules s x))

  where
  root = case x of
           ImpTop r    -> r
           ImpNested n -> nameTopModule n

--------------------------------------------------------------------------------


{- | Try to resolve an import. If the imported module can be resolved,
and it refers to a module that's already been resolved, then we do the
import and extend the current scoping environment.  Otherwise, we just
queue the import back on the @modImports@ of the current module to be tried
again later.-}
tryImport :: CurState -> ImportG (ImpName PName) -> CurState
tryImport s imp =
  fromMaybe (updCur s (pushImport imp))   -- not ready, put it back on the q
  do let srcName = iModule imp
     mname <- knownImpName s srcName
     ext   <- knownModule s mname

     let isPub x = x `Set.member` rmodPublic ext
         new = case rmodKind ext of
                 AModule    -> interpImportEnv imp
                                 (filterUNames isPub (rmodDefines ext))
                 AFunctor   -> mempty
                 ASignature -> mempty

     pure $ updCurMS s { changes = True }
            \ms -> ms { modImported = new <> modImported ms }

-- | Resolve all imports in the current modules
doImportStep :: CurState -> CurState
doImportStep s = foldl' tryImport s1 (modImports (curMod s))
  where
  s1 = updCur s \m -> m { modImports = [] }


{- | Try to instantiate a functor.  This succeeds if we can resolve the functor
and the arguments and the both refer to already resolved names.
Note: at the moment we ignore the arguments, but we'd have to do that in
order to implment applicative behavior with caching. -}
tryInstanceMaybe ::
  HasCurScope a =>
  CurState' a ->
  ImpName Name ->
  (ImpName PName, ModuleInstanceArgs PName)
  {- ^ Functor and arguments -}  ->
  Maybe (ResolvedLocal,CurState' a)
tryInstanceMaybe s mn (f,_xs) =
  do fn <- knownImpName s f
     let path = case mn of
                  ImpTop m    -> TopModule m
                  ImpNested m ->
                    case asOrigName m of
                      Just og -> Nested (ogModule og) (ogName og)
                      Nothing ->
                        panic "tryInstanceMaybe" [ "Not a top-level name" ]
     doInstantiateByName False path fn s

{- | Try to instantiate a functor.  If successful, then the newly instantiated
module (and all things nested in it) are going to be added to the
@doneModules@ field.  Otherwise, we queue up the instantiatation in
@curMod@ for later processing -}
tryInstance ::
  CurState ->
  Name ->
  (ImpName PName, ModuleInstanceArgs PName) ->
  CurState
tryInstance s mn (f,xs) =
  case tryInstanceMaybe s (ImpNested mn) (f,xs) of
    Nothing       -> updCur s (pushInst mn (f,xs))
    Just (def,s1) -> s1 { changes = True
                        , doneModules = Map.insert mn def (doneModules s1)
                        }

{- | Generate a fresh instance for the functor with the given name. -}
doInstantiateByName ::
  HasCurScope a =>
  Bool
  {- ^ This indicates if the result is a functor or not.  When instantiating
    a functor applied to some arguments the result is not a functor.  However,
    if we are instantiating a functor nested within some functor that's being
    instantiated, then the result is still a functor. -} ->
  ModPath {- ^ Path for instantiated names -} ->
  ImpName Name {- ^ Name of the functor/module being instantiated -} ->
  CurState' a -> Maybe (ResolvedLocal,CurState' a)

doInstantiateByName keepArgs mpath fname s =
  do def <- knownModule s fname
     pure (doInstantiate keepArgs mpath def s)



{- | Generate a new instantiation of the given module/signature.
Note that the module might not be a functor itself (e.g., if we are
instantiating something nested in a functor -}
doInstantiate ::
  HasCurScope a =>
  Bool               {- ^ See `doInstantiateByName` -} ->
  ModPath            {- ^ Path for instantiated names -} ->
  ResolvedExt        {- ^ The thing being instantiated -} ->
  CurState' a -> (ResolvedLocal,CurState' a)
doInstantiate keepArgs mpath def s = (newDef, Set.foldl' doSub newS nestedToDo)
  where
  ((newEnv,newNameSupply),nestedToDo) =
      M.runId
    $ M.runStateT Set.empty
    $ runSupplyT (nameSupply s)
    $ travNamingEnv instName
    $ rmodDefines def

  newS = s { nameSupply = newNameSupply }

  pub = let inst = zipByTextName (rmodDefines def) newEnv
        in Set.fromList [ case Map.lookup og inst of
                            Just newN -> newN
                            Nothing -> panic "doInstantiate.pub"
                                           [ "Lost a name", show og ]
                        | og <- Set.toList (rmodPublic def)
                        ]


  newDef = ResolvedModule { rmodDefines   = newEnv
                          , rmodPublic    = pub
                          , rmodKind      = case rmodKind def of
                                              AFunctor ->
                                                 if keepArgs then AFunctor
                                                             else AModule
                                              ASignature -> ASignature
                                              AModule -> AModule

                          , rmodNested    = Set.map snd nestedToDo
                          , rmodImports   = mempty
                            {- we don't do name resolution on the instantiation
                               the usual way: instead the functor and the
                               arguments are renamed separately, then we
                               we do a pass where we replace:
                                  defined names of functor by instantiations
                                  parameter by actual names in arguments.
                            -}
                          }

  doSub st (oldSubName,newSubName) =
    case doInstantiateByName True (Nested mpath (nameIdent newSubName))
                                  (ImpNested oldSubName) st of
      Just (idef,st1) -> st1 { doneModules = Map.insert newSubName idef
                                                        (doneModules st1) }
      Nothing  -> panic "doInstantiate.doSub"
                    [ "Missing nested module:", show (pp oldSubName) ]

  instName :: Name -> SupplyT (M.StateT (Set (Name,Name)) M.Id) Name
  instName x =
    do y <- liftSupply (freshNameFor mpath x)
       when (x `Set.member` rmodNested def)
            (M.lift (M.sets_ (Set.insert (x,y))))
       pure y


-- | Try to make progress on all instantiations.
doInstancesStep :: CurState -> CurState
doInstancesStep s = Map.foldlWithKey' tryInstance s0 (modInstances (curMod s))
  where
  s0 = updCur s \m' -> m' { modInstances = Map.empty }

tryFinishCurMod :: Todo -> CurState -> Maybe ResolvedLocal
tryFinishCurMod m newS
  | isDone newM =
    Just ResolvedModule
           { rmodDefines = modDefines m
           , rmodPublic  = modPublic m
           , rmodKind    = modKind m
           , rmodNested  = Set.unions
                             [ Map.keysSet (modInstances m)
                             , Map.keysSet (modMods m)
                             ]
           , rmodImports  = modImported (modState newM)
           }

  | otherwise = Nothing
  where newM = curMod newS


-- | Try to resolve the "normal" module with the given name.
tryModule :: CurState -> Name -> Todo -> CurState
tryModule s nm m =
  case tryFinishCurMod m newS of
    Just rMod ->
      newS { curMod      = curMod s
           , doneModules = Map.insert nm rMod (doneModules newS)
           , changes     = True
           }
    Nothing -> newS { curMod = pushMod nm newM (curMod s) }
  where
  s1     = updCur s \_ -> updMS (\ms -> ms { modOuter = curScope s }) m
  newS   = doModuleStep s1
  newM   = curMod newS

-- | Process all submodules of a module.
doModulesStep :: CurState -> CurState
doModulesStep s = Map.foldlWithKey' tryModule s0 (modMods m)
  where
  m  = curMod s
  s0 = s { curMod = m { modMods = mempty } }



-- | All steps involved in processing a module.
doModuleStep :: CurState -> CurState
doModuleStep = doStep step
  where
  step = doStep doModulesStep
       . doStep doInstancesStep
       . doStep doImportStep



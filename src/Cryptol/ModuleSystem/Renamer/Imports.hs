{- |

This module deals with imports of nested modules (@import submodule@)
The issue is that in @import submodule X@ we need to resolve what @X@
referes to before we know what it will import.

Even triciker is the case for functor instantiations, @F { X }@:
in this case we have to first resolve @F@ and @X@, and then generate
fresh names for the instance (or reusing an existing instantiation if
we are going for applicative semantics).

We assume that declarations can be ordered in dependency order,
and submodules can be processed one at a time (i.e., no recursion across
modules).  Thus, the following is OK:

module A where
  x = 0x2

  submodule B where
    y = x

  z = B::y


However, this is not OK:

  submodule A = F X
  submodule F where
    import A

In particular, this means that a functor may not depend on its own
instantiation.
-}

{-# Language BlockArguments #-}
module Cryptol.ModuleSystem.Renamer.Imports where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List(foldl')
import Control.Monad(when,mplus)
import qualified MonadLib as M

import Cryptol.Utils.PP(pp)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(ModPath(..),Namespace(..))

import Cryptol.Parser.Position(Located(..))
import Cryptol.Parser.AST
  ( Module, ModuleG(..), ModuleDefinition(..)
  , ImportG(..),PName
  , ModuleInstanceArgs(..), ModuleInstanceArg(..)
  , ImpName(..)
  )
import Cryptol.ModuleSystem.Binds (OwnedEntities(..), Mod(..), TopDef(..))
import Cryptol.ModuleSystem.Name
          ( Name, Supply, SupplyT, runSupplyT, liftSupply, freshNameFor)
import Cryptol.ModuleSystem.Names(Names(..))
import Cryptol.ModuleSystem.NamingEnv
          ( NamingEnv(..), lookupNS, shadowing, travNamingEnv
          , interpImportEnv )


data ModState = ModState
  { modOuter        :: NamingEnv
  , modImported     :: NamingEnv
  , modImportOrder  :: [PName]
  }

emptyModState :: ModState
emptyModState = ModState
  { modOuter        = mempty
  , modImported     = mempty
  , modImportOrder  = []
  }

type Todo = Mod ModState

-- | Initial state of a module that needs processing.
todoModule :: Mod () -> Todo
todoModule = fmap (const emptyModState)

isDone :: Todo -> Bool
isDone m = null     (modImports m)   &&
           Map.null (modInstances m) &&
           Map.null (modSigs m)      &&
           Map.null (modMods m)

pushImport :: ImportG (ImpName PName) -> Todo -> Todo
pushImport i m = m { modImports = i : modImports m }

pushInst :: Name -> (ImpName PName, ModuleInstanceArgs PName) -> Todo -> Todo
pushInst k v m = m { modInstances = Map.insert k v (modInstances m) }

pushMod :: Name -> Todo -> Todo -> Todo
pushMod k v m = m { modMods = Map.insert k v (modMods m) }

updMS :: (ModState -> ModState) -> Todo -> Todo
updMS f m = m { modState = f (modState m) }



{- | This represents a resolved module or signaure.
Note that signaures are never "imported", however we do need to keep them
here so that signatures in a functor are properly instantiated when
the functor is instantiated. -}
data ResolvedModule imps = ResolvedModule
  { rmodDefines   :: NamingEnv    -- ^ Things defined by the module/signature.
  , rmodParams    :: Bool         -- ^ Is it a functor
  , rmodNested    :: Set Name     -- ^ Modules and signatures nested in this one
  , rmodImpOrder  :: imps
    {- ^ Process imports in this order
    Also, top-level imports can (and should) always be processed before
    local ones.  External modules need not specify this field,
    it is just part of the thing we compute for local modules. -}
  }

forget :: ResolvedModule [PName] -> ResolvedModule ()
forget r = r { rmodImpOrder = () }


data CurState = CurState
  { curMod      :: Todo
    -- ^ This is what needs to be done

  , externalModules :: Map (ImpName Name) (ResolvedModule ())
    -- ^ Modules defined outside the current top-level modules

  , doneModules :: Map Name (ResolvedModule [PName])
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

curScope :: CurState -> NamingEnv
curScope s = modDefines m `shadowing` modImported ms `shadowing` modOuter ms
  where
  m   = curMod s
  ms  = modState m

knownPName :: CurState -> PName -> Maybe Name
knownPName s x =
  do ns <- lookupNS NSModule x (curScope s)
     case ns of
       One n    -> pure n
       -- NOTE: since we build up what's in scope incrementally,
       -- it is possible that this would eventually be ambiguous,
       -- which we'll detect during actual renaming.

       Ambig {} -> Nothing

knownImpName :: CurState -> ImpName PName -> Maybe (ImpName Name)
knownImpName s i =
  case i of
    ImpTop m    -> pure (ImpTop m)
    ImpNested m -> ImpNested <$> knownPName s m

knownModule :: CurState -> ImpName Name -> Maybe (ResolvedModule ())
knownModule s x =
  Map.lookup x (externalModules s) `mplus`
  case x of
    ImpNested y -> forget <$> Map.lookup y (doneModules s)
    ImpTop {}   -> Nothing

--------------------------------------------------------------------------------


{- | Try to resolve an import. If the imported module can be resolved,
and it refers to a module that's already been resolved, then we do the
import and extend the current scoping environment.  Otherwise, we just
queue the import back on the @modImports@ of the current module to be tried
again later.-}
tryImport :: CurState -> ImportG (ImpName PName) -> CurState
tryImport s imp =
  case knownModule s =<< knownImpName s (iModule imp) of

    Nothing -> updCur s (pushImport imp)

    Just ext ->
      let new = if rmodParams ext
                  then mempty  -- imported a functor, error reported later
                  else interpImportEnv imp (rmodDefines ext)
      in updCurMS s { changes = True }
           \ms -> ms { modImported = new <> modImported ms
                     , modImportOrder =
                         case iModule imp of
                         ImpNested x -> x : modImportOrder ms
                         _           ->     modImportOrder ms
                     }

-- | Keep resolving imports until we can't make any more progress
doImports :: CurState -> CurState
doImports s = if changes s2 then doImports s2 else s2
  where
  is = modImports (curMod s)
  s1 = updCur s { changes = False } \m -> m { modImports = [] }
  s2 = foldl' tryImport s1 is


{- | Try to instantiate a functor.  This succeeds if we can resolve the functor
and the arguments and the both refer to already resolved names.
Note: at the moment we ignore the arguments, but we'd have to do that in
order to implment applicative behavior throuhg caching. -}
tryInstanceMaybe ::
  CurState ->
  (ImpName PName, ModuleInstanceArgs PName)
  {- ^ Functor and arguments -}  ->
  Maybe (ResolvedModule [PName],CurState)
tryInstanceMaybe s (f,_xs) =
  do fn <- knownImpName s f
     doInstantiateByName False fn s

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
  case tryInstanceMaybe s (f,xs) of
    Nothing       -> updCur s (pushInst mn (f,xs))
    Just (def,s1) -> s1 { changes = True
                        , doneModules = Map.insert mn def (doneModules s1)
                        }

{- | Generate a fresh instance for the functor with the given name. -}
doInstantiateByName ::
  Bool
  {- ^ This indicates if the result is a functor or not.  When instantiating
    a functor applied to some arguments the result is not a functor.  However,
    if we are instantiating a functor nested withing some functor that's being
    instantiated, then the result is still a functor. -} ->
  ImpName Name {- ^ Name for the functor/module -} ->
  CurState -> Maybe (ResolvedModule [PName],CurState)

doInstantiateByName keepArgs mname s =
  do def <- knownModule s mname
     pure (doInstantiate keepArgs def s)



{- | Generate a new instantiation of the given module/signature.
Note that the module might not be a functor itself (e.g., if we are
instantiating something nested in a functor -}
doInstantiate ::
  Bool               {- ^ See @doInstantiateByName@ -} ->
  ResolvedModule ()  {- ^ The thing being instantiated -} ->
  CurState -> (ResolvedModule [PName],CurState)
doInstantiate keepArgs def s = (newDef, Set.foldl' doSub newS nestedToDo)
  where
  ((newEnv,newNameSupply),nestedToDo) =
      M.runId
    $ M.runStateT Set.empty
    $ runSupplyT (nameSupply s)
    $ travNamingEnv instName
    $ rmodDefines def

  newS = s { nameSupply = newNameSupply }

  newDef = ResolvedModule { rmodDefines   = newEnv
                          , rmodParams    = if keepArgs
                                              then rmodParams def
                                              else False
                          , rmodNested    = Set.map snd nestedToDo
                          , rmodImpOrder  = []
                            {- we don't do name resolution on the instantiation
                               the usual way: instead the functor and the
                               arguments are renamed separately, then we
                               we do a pass where we replace:
                                  defined names of functor by instantiations
                                  parameter by actual names in arguments.
                            -}
                          }

  doSub st (oldSubName,newSubName) =
    case doInstantiateByName True (ImpNested oldSubName) st of
      Just (idef,st1) -> st1 { doneModules = Map.insert newSubName idef
                                                        (doneModules st1) }
      Nothing  -> panic "doInstantiate.doSub"
                    [ "Missing nested module:", show (pp oldSubName) ]

  instName :: Name -> SupplyT (M.StateT (Set (Name,Name)) M.Id) Name
  instName x =
    do y <- liftSupply (freshNameFor x)
       when (x `Set.member` rmodNested def)
            (M.lift (M.sets_ (Set.insert (x,y))))
       pure y


{- | ^ Keep insantiating things until we can't make any more progres -}
doInstances :: CurState -> CurState
doInstances s = Map.foldlWithKey' tryInstance s0 (modInstances m)
  where
  m  = curMod s
  s0 = updCur s \m' -> m' { modInstances = Map.empty }


-- | Generate names for signatures.  This always succeeds.
doSignatures :: CurState -> CurState
doSignatures s = updCur s1 \m -> m { modSigs = mempty }
  where
  s1 = s { doneModules = Map.union resolved (doneModules s)
         , changes     = not (Map.null sigs)
         }

  sigs      = modSigs (curMod s)
  resolved  = doSig <$> sigs
  doSig sig = ResolvedModule { rmodDefines  = sig
                             , rmodNested   = mempty
                             , rmodParams   = False
                             , rmodImpOrder = []
                                -- no imports in signatures, at least for now.
                             }


-- | Try to resolve the "normal" module with the given name.
tryModule :: CurState -> Name -> Todo -> CurState
tryModule s nm m
  | isDone newM =
    newS { curMod      = curMod s
         , doneModules = Map.insert nm rMod (doneModules newS)
         , changes     = True
         }
  | otherwise = newS { curMod = pushMod nm newM (curMod s) }
  where
  s1     = updCur s \_ -> updMS (\ms -> ms { modOuter = curScope s }) m
  newS   = doModuleStep s1
  newM   = curMod newS

  rMod   = ResolvedModule
             { rmodDefines = modDefines m
             , rmodParams  = modParams m
             , rmodNested  = Set.unions
                               [ Map.keysSet (modInstances m)
                               , Map.keysSet (modSigs m)
                               , Map.keysSet (modMods m)
                               ]
             , rmodImpOrder = reverse (modImportOrder (modState m))
             }

-- | Process all submodules of a module.
doModules :: CurState -> CurState
doModules s = Map.foldlWithKey' tryModule s0 (modMods m)
  where
  m  = curMod s
  s0 = s { curMod = m { modMods = mempty } }



-- | Keep progressing in the various sub-components of the current module,
-- until we can't make any more progress.
doModuleStep :: CurState -> CurState
doModuleStep s0 = if changes s1 then doModuleStep s1 else s0
  where
  step = doModules . doInstances . doSignatures . doImports
  s1   = step s0



doTopDef ::
  Map (ImpName Name) (ResolvedModule ()) ->
  TopDef ->
  Supply ->
  Maybe (Map Name (ResolvedModule [PName]), Supply)
doTopDef ext def su =
  case def of
    TopMod m mo ->
      let s = doModules CurState
                          { curMod = todoModule mo
                          , externalModules = ext
                          , doneModules = mempty
                          , nameSupply = su
                          , changes = False
                          }
      in if isDone (curMod s) then Just (doneModules s, nameSupply s)
                              else Nothing -- XXX: better error


    TopInst m f as -> undefined
    TopInstOld m f a -> undefined




--------------------------------------------------------------------------------

data OpenLoopState = OpenLoopState
  { unresolvedOpen  :: [ImportG PName]
  , scopeImports    :: NamingEnv   -- names from open/impot
  , scopeDefs       :: NamingEnv   -- names defined in this module
  , scopingRel      :: NamingEnv   -- defs + imports with shadowing
                                   -- (just a cache of `scopeImports+scopeDefs`)
  , openLoopChange  :: Bool
  }


{- | Complete the set of import using @import submodule@ declarations.
This should terminate because on each iteration either @unresolvedOpen@
decreases or @openLoopChange@ remians @False@. We don't report errors
here, as they will be reported during renaming anyway. -}
openLoop ::
  OwnedEntities   {- ^ Definitions of all known nested things -} ->
  NamingEnv       {- ^ Definitions of the module (these shadow) -} ->
  [ImportG PName] {- ^ Open declarations                        -} ->
  NamingEnv       {- ^ Imported declarations                    -} ->
  NamingEnv       {- ^ Completed imports                        -}
openLoop modEnvs defs os imps =
  scopeImports $
  loop OpenLoopState  { unresolvedOpen = os
                      , scopeImports   = imps
                      , scopeDefs      = defs
                      , scopingRel     = defs `shadowing` imps
                      , openLoopChange = True
                      }
  where
  loop s
    | openLoopChange s =
      loop $ foldl' (processOpen modEnvs)
                    s { unresolvedOpen = [], openLoopChange = False }
                    (unresolvedOpen s)
    | otherwise = s






{- | Processing of a single @import submodule@ declaration
Notes:
  * ambiguity will be reported later when we do the renaming
  * assumes scoping only grows, which should be true
  * in case of ambiguous import, we are not adding the names from *either*
    of the imports so this may give rise to undefined names, so we may want to
    suppress reporing undefined names if there ambiguities for
    module names.  Alternatively we could add the defitions from
    *all* options, but that might lead to spurious ambiguity errors.
-}
processOpen :: OwnedEntities -> OpenLoopState -> ImportG PName -> OpenLoopState
processOpen modEnvs s o =
  case lookupNS NSModule (iModule o) (scopingRel s) of
    Nothing -> s { unresolvedOpen = o : unresolvedOpen s }
    Just (One n) ->
      case Map.lookup n (ownSubmodules modEnvs) of
        Nothing

          | Just (f,args) <- Map.lookup n (ownInstances modEnvs) ->
            let scope = scopingRel s
            in
            case (,) <$> tryLookup scope f <*> tryLookupArgs scope args of
              Nothing -> s    -- not yet ready
              Just (f',args') -> undefined -- ready to isntantiate

          | otherwise ->
            panic "openLoop" [ "Missing defintion for module", show n ]


        Just def ->
          let new     = interpImportEnv o def
              newImps = new <> scopeImports s
          in s { scopeImports   = newImps
               , scopingRel     = scopeDefs s `shadowing` newImps
               , openLoopChange = True
               }
    Just (Ambig _) -> s


tryLookupArgs ::
  NamingEnv -> ModuleInstanceArgs PName -> Maybe (ModuleInstanceArgs Name)
tryLookupArgs env args =
  case args of
    DefaultInstArg x -> DefaultInstArg <$> tryLookup env x
    NamedInstArgs xs -> NamedInstArgs <$> mapM (tryLookupArg env) xs

tryLookup ::
  NamingEnv -> Located (ImpName PName) -> Maybe (Located (ImpName Name))
tryLookup env lin =
  case thing lin of
    ImpTop y -> pure lin { thing = ImpTop y }
    ImpNested x ->
      do ns <- lookupNS NSModule x env
         case ns of
           One n -> pure lin { thing = ImpNested n }
           _     -> Nothing

tryLookupArg ::
  NamingEnv -> ModuleInstanceArg PName -> Maybe (ModuleInstanceArg Name)
tryLookupArg env (ModuleInstanceArg a x) =
  ModuleInstanceArg a <$> tryLookup env x





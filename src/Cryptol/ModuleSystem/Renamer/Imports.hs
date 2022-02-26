{- |

This module deals with imports of nested modules (@import submodule@)
The issue is that in @import submodule X@ we need to resolve what @X@
referes to before we know what it will import.

Even triciker is the case for functor instantiations, @F { X }@:
in this case we have to first resolve @F@ and @X@, and then generate
fresh names for the instance (or reusing an existing instantiation if
we are going for applicative semantics).
-}
module Cryptol.ModuleSystem.Renamer.Imports where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List(foldl')
import Control.Monad(when)
import MonadLib(StateT,sets_,runStateT,Id,runId,lift)

import Cryptol.Utils.PP(pp)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(Namespace(..))

import Cryptol.Parser.Position(Located(..))
import Cryptol.Parser.AST
  ( ImportG(..),PName, ModuleInstanceArgs(..), ModuleInstanceArg(..)
  , ImpName(..)
  )
import Cryptol.ModuleSystem.Binds(OwnedEntities(..))
import Cryptol.ModuleSystem.Name
          (Name, Supply, SupplyT, runSupplyT, liftSupply, freshNameFor)
import Cryptol.ModuleSystem.Names(Names(..))
import Cryptol.ModuleSystem.NamingEnv
          ( NamingEnv(..), lookupNS, shadowing, travNamingEnv
          , interpImportEnv )

{-
Note: we assume that declarations can be ordered in dependency order,
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


-- | Unresolved module
data Mod = Mod
  { modImports   :: [ ImportG (ImpName PName) ]
  , modParams    :: Bool -- True = has params
  , modInstances :: Map Name (ImpName PName, ModuleInstanceArgs PName)
  , modMods      :: Map Name Mod
  , modDefines   :: NamingEnv  -- ^ Things defined by this module
  }

isEmptyMod :: Mod -> Bool
isEmptyMod m = null (modImports m) &&
               Map.null (modInstances m) &&
               Map.null (modMods m)

data ResolvedModule = ResolvedModule
  { rmodDefines :: NamingEnv    -- ^ Things defined by the module
  , rmodParams  :: Bool         -- ^ Is it a functor
  , rmodNested  :: Set Name     -- ^ Modules nested in this one
  }


data CurState = CurState
  { curScope    :: NamingEnv
    -- ^ What names are currently in scope

  , curMod      :: Mod
    -- ^ This is what needs to be done

  , doneModules :: Map (ImpName Name) ResolvedModule
    {- ^ These are modules that are fully resolved.
      Includes all modules we know about: external, nested in other
      modules, etc. 
      Note: we only add a module here, if all of its nested modules are also
            resolved.
    -}

  , nameSupply  :: Supply
    -- ^ Use this to instantiate functors

  , changes :: Bool
    -- ^ True if something changed on the last iteration
  }

definedHere :: CurState -> Name -> Bool
definedHere s x = x `Map.member` modInstances me || x `Map.member` modMods me
  where me = curMod s

knownPName :: CurState -> PName -> Maybe Name
knownPName s x =
  do ns <- lookupNS NSModule x (curScope s)
     case ns of
       One n    -> pure n
       Ambig xs -> fst <$> Set.minView (Set.filter (definedHere s) xs)
          -- XXX: if still ambiguous, we should probably just stop and report
          -- error

knownImpName :: CurState -> ImpName PName -> Maybe (ImpName Name)
knownImpName s i =
  case i of
    ImpTop m    -> pure (ImpTop m)
    ImpNested m -> ImpNested <$> knownPName s m

knownModule :: CurState -> ImpName Name -> Maybe ResolvedModule
knownModule s x = Map.lookup x (doneModules s)

{- | Try to resolve an import full.  Either add the resulting names to
the current scope, or add it back to the current to the @curMod@ -}
tryImport :: CurState -> ImportG (ImpName PName) -> CurState
tryImport s imp =
  case knownModule s =<< knownImpName s (iModule imp) of

    Nothing ->
      let m = curMod s
      in s { curMod = m { modImports = imp : modImports m } }

    Just m
      | not (rmodParams m) ->
        s { curScope = interpImportEnv imp (rmodDefines m) <> curScope s
          , changes = True
          }
      | otherwise -> s { changes = True }
        -- ^ imported a functor.  consider resolved, but imports nothing
        -- presumably this will lead to an error later?

-- | Keep resolving imports until we can't make any more progress
doImports :: CurState -> CurState
doImports s = if changes s2 then doImports s2 else s2
  where
  is = modImports (curMod s)
  m  = curMod s
  s1 = s { changes = False, curMod = m { modImports = [] } }
  s2 = foldl' tryImport s1 is


-- XXX: generalize so that it can work with top-level modules that are
-- instances.
tryInstance ::
  CurState ->
  Name ->
  (ImpName PName, ModuleInstanceArgs PName) ->
  CurState
tryInstance s mn (f,xs) =
  case known of
    Nothing ->
      s { curMod = m { modInstances = Map.insert mn (f,xs) (modInstances m) } }
    Just s1 -> s1
  where
  m = curMod s
  known =
    do fn <- knownImpName s f
       doInstantiateByName False mn fn s

doInstantiateByName ::
  Bool -> Name -> ImpName Name -> CurState -> Maybe CurState
doInstantiateByName keepArgs newName mname s =
  do def <- Map.lookup mname (doneModules s)
     pure (doInstantiate keepArgs newName def s)

{- | Generate a new instantiation of the given module.
Note that the module might not be a functor itself (e.g., if we are
instantiating something nested in a functor -}
doInstantiate :: Bool -> Name -> ResolvedModule -> CurState -> CurState
doInstantiate keepArgs newName def s = Set.foldl' doSub newS nestedToDo
  where
  ((newEnv,newNameSupply),nestedToDo) =
      runId
    $ runStateT Set.empty
    $ runSupplyT (nameSupply s)
    $ travNamingEnv instName
    $ rmodDefines def

  newDef = ResolvedModule { rmodDefines = newEnv
                          , rmodParams  = if keepArgs
                                            then rmodParams def
                                            else False
                          , rmodNested  = Set.map snd nestedToDo
                          }

  newS = s { changes     = True
           , doneModules = Map.insert (ImpNested newName) newDef (doneModules s)
           , nameSupply  = newNameSupply
           }


  doSub st (oldSubName,newSubName) =
    case doInstantiateByName True newSubName (ImpNested oldSubName) st of
      Just st1 -> st1
      Nothing  -> panic "doInstantiate.doSub"
                    [ "Missing nested module:", show (pp oldSubName) ]

  instName :: Name -> SupplyT (StateT (Set (Name,Name)) Id) Name
  instName x =
    do y <- liftSupply (freshNameFor x)
       when (x `Set.member` rmodNested def)
            (lift (sets_ (Set.insert (x,y))))
       pure y


doInstances :: CurState -> CurState
doInstances s = Map.foldlWithKey' tryInstance s0 (modInstances m)
  where
  m  = curMod s
  s0 = s { curMod = m { modInstances = Map.empty } }


resolveMod :: Mod -> ResolvedModule
resolveMod m = ResolvedModule
  { rmodDefines = modDefines m
  , rmodParams  = modParams m
  , rmodNested  = Map.keysSet (modInstances m) `Set.union`
                  Map.keysSet (modMods m)
  }


tryModule :: CurState -> Name -> Mod -> CurState
tryModule s nm m
  | isEmptyMod newM =
    newS { curScope    = curScope s
         , curMod      = topMod
         , doneModules = Map.insert (ImpNested nm) r (doneModules newS)
         , changes     = True
         }
  | otherwise =
    newS { curScope = curScope s
         , curMod = topMod { modMods = Map.insert nm newM (modMods topMod) }
         }

  where
  topMod = curMod s
  r      = resolveMod m

  newS = doModuleStep s { curMod = m
                        , curScope = rmodDefines r `shadowing` curScope s
                        }

  newM = curMod newS


doModuleStep :: CurState -> CurState
doModuleStep = doModules . doInstances . doImports


doModules :: CurState -> CurState
doModules s = Map.foldlWithKey' tryModule s0 (modMods m)
  where
  m  = curMod s
  s0 = s { curMod = m { modMods = mempty } }

topModuleLoop :: CurState -> CurState
topModuleLoop s = if changes s1 then topModuleLoop s1 else s
  where s1 = doModules s

-- | Given the definitions of external modules, computes what is defined
-- by all local modules, including instantiations.
-- XXX: we may be able to compute what's in scope in all modules too, to
-- avoid having to do it again later.
topModule ::
  Map (ImpName Name) ResolvedModule ->
  m -> {- XXX -}
  Supply ->
  (Map (ImpName Name) ResolvedModule, Supply)
topModule externalModules m supply = (doneModules result, nameSupply result)
  where
  result = topModuleLoop
              CurState { curScope    = mempty
                       , curMod      = theMod
                       , doneModules = externalModules
                       , nameSupply  = supply
                       , changes     = False
                       }

  theMod = Mod { modImports   = undefined
               , modParams    = undefined
               , modDefines   = undefined
               , modInstances = undefined
               , modMods      = undefined
               }
{-
  { modImports   :: [ ImportG (ImpName PName) ]
  , modParams    :: Bool -- True = has params
  , modInstances :: Map Name (ImpName PName, ModuleInstanceArgs PName)
  , modMods      :: Map Name Mod
  , modDefines   :: NamingEnv  -- ^ Things defined by this module
-}



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





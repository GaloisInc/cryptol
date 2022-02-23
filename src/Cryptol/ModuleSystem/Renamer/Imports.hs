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

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(Namespace(..),ModName)

import Cryptol.Parser.Position(Located(..))
import Cryptol.Parser.AST
  ( ImportG(..),PName, ModuleInstanceArgs(..), ModuleInstanceArg(..)
  , ImpName(..)
  )
import Cryptol.ModuleSystem.Binds(OwnedEntities(..), interpImportEnv)
import Cryptol.ModuleSystem.Name(Name, Supply)
import Cryptol.ModuleSystem.Names(Names(..))
import Cryptol.ModuleSystem.NamingEnv(NamingEnv(..), lookupNS, shadowing)


{- | Information about what's in scope in a module.  -}
data Scope = Scope
  { letDefs           :: NamingEnv      -- ^ Things defined in the module
  , letTopImports     :: NamingEnv      -- ^ Things imported externally
  , mutNestedImports  :: NamingEnv      -- ^ Things from imported submodules
  }

-- | Compute the actual scoping environment for a module, based on the
-- current approximation.
getScope :: Scope -> NamingEnv
getScope x = letDefs x `shadowing` (letTopImports x <> mutNestedImports x)

-- | Add some extra names that came through a submodule import
extScopeWith :: NamingEnv -> Scope -> Scope
extScopeWith e s = s { mutNestedImports = e <> mutNestedImports s }

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

data Mod = Mod
  { modImports   :: [ ImportG (ImpName PName) ]
  , modInstances :: Map Name (ImpName PName, ModuleInstanceArgs PName)
  , modMods      :: Map Name Mod
  }

isEmptyMod :: Mod -> Bool
isEmptyMod m = null (modImports m) &&
               Map.null (modInstances m) &&
               Map.null (modMods m)



data CurState = CurState
  { curScope    :: NamingEnv
    -- ^ only module name space matters

  , curMod      :: Mod
    -- ^ This is what needs to be done

  , doneModules :: Map (ImpName Name) NamingEnv
    {- ^ These are modules that are fully resolved.
      Includes all modules we know about: external, nested in other
      modules, etc.
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
       One x    -> pure x
       Ambig xs -> fst <$> Set.minView (Set.filter (definedHere s) xs)
          -- XXX: if still ambiguous, we should probably just stop and report
          -- error

knownImpName :: CurState -> ImpName PName -> Maybe (ImpName Name)
knownImpName s i =
  case i of
    ImpTop m    -> pure (ImpTop m)
    ImpNested i -> ImpNested <$> knownPName s i

knownModule :: CurState -> ImpName Name -> Maybe NamingEnv
knownModule s x = Map.lookup x (doneModules s)

{- | Try to resolve an import full.  Either add the resulting names to
the current scope, or add it back to the current to the @curMod@ -}
tryImport :: CurState -> ImportG (ImpName PName) -> CurState
tryImport s imp =
  case knownModule s =<< knownImpName s (iModule imp) of
    Nothing -> let m = curMod s
               in s { curMod = m { modImports = imp : modImports m } }
    Just ns -> s { curScope = ns <> curScope s, changes = True }

-- | Keep resolving imports until we can't make any more progress
doImports :: CurState -> CurState
doImports s = if changes s2 then doImports s2 else s2
  where
  is = modImports (curMod s)
  m  = curMod s
  s1 = s { changes = False, curMod = m { modImports = [] } }
  s2 = foldl' tryImport s1 is


tryInstance ::
  CurState ->
  (ImpName PName, (ImpName PName, ModuleInstanceArgs PName)) ->
  CurState
tryInstance s (mn,(f,xs)) =
  case mb of
    Nothing ->
      s { curMod = m { modInstances = Map.insert mn (f,xs) (modInstances m) } }
    Just (env,sup) ->
      s { nameSupply  = sup
        , changes     = True
        , doneModules = Map.insert mn env
        }
  where
  m = curMod s

  mb = do fn <- knownImpName s f
          fm <- knownModule  s fn
          xn <- tryLookupArg (curScope s) xs
          undefined

{-
tryFinishMod :: CurState -> Maybe (CurState, NamingEnv)
tryFinishMod s
  | isEmptyMod (curMod s) = Just (env, s)
  where
  env = singletonNS NSModule 
wn
-}



{-
--------------------------------------------------------------------------------
-- | Whose imports are we talking about
data MName = TopM             -- ^ The top levelmodule
           | NestedM Name     -- ^ One of the submodules
  deriving (Show,Eq,Ord)

-- | Information about the current state of the approximating computation
data AllModuleState = AllModuleState
  { letMe         :: ModName
    {- ^ Top-level name of module in which we work -}

  , mutDefs       :: Map (ImpName Name) BoundNames
    {- ^ Names defined in modules (functors and non-functors) and signature.
         This is mutbale because when we instantiate a functor we added it
         (and things nested in it) to this field.
     -}

  , mutModules    :: Map MName Scope
    {- ^ Keeps track of the current approximation to what's in scope in
         all known modules -}

  , mutUnresolved :: [(MName,ImportG PName)]
    {- ^ Submodule imports that have not been resolved yet. -}

  , mutUnresolvedInstances ::
      [ (MName, Name, Located (ImpName PName), ModuleInstanceArgs PName) ]
    {- ^ Submodules that need to be instantiated (M = F A). -}

  , mutChanges    :: Bool
    {- ^ Indicates if anything changed on the last iteration. -}
  }
-}


{-
Nesting of modules is important for two reasons:

  1. To determine how to propagate imported names:

      import submodule A
      submodule B where
        ... things imported from A are in scope here

  2. When instantiating a functor, we also need need to instantiate all
     the things nested in it.

     submodule F where
       import signature S
       submodule P where
         ...

    submodule M = F X


There are some subtleties here:
  * if new stuff comes through an import A, it and goes to a F,
    it also needs to go to all instantiations of F, even though they might
    not be statically nested.  For example:

  submodule M where
    import A
    submodule F where
      import signature S

  submodule C = F X

  stuff imported from A is in scope in the concrete definition of 





-}


{-
toImpName :: AllModuleState -> MName -> ImpName Name
toImpName s m =
  case m of
    TopM      -> ImpTop (letMe s)
    NestedM n -> ImpNested n

{- | Add some new names to the given module.
The names are also propagate to modules nested within the original one. -}
extScopeOf :: MName -> NamingEnv -> AllModuleState -> AllModuleState
extScopeOf m e s = foldr extend s1 nested
  where
  s1        = s { mutModules = Map.adjust (extScopeWith e) m (mutModules s)
                , mutChanges = True
                  {- It is possible that nothing actually changed.
                     For termination this is OK, because we only do this
                     when we eliminate an import, so the measure is the
                     number of imports that remain to be processed -}
                }
  nested    = Map.findWithDefault [] (toImpName s1 m) (mutNesting s)
  extend n  = extScopeOf (NestedM n) e

{- | Get the scoping environment for a particular module. -}
scopeOf :: MName -> AllModuleState -> NamingEnv
scopeOf m s =
  case Map.lookup m (mutModules s) of
    Just ms -> getScope ms
    Nothing -> panic "scopeOf" [ "Missing module: " ++ show m ]

{- | Try to resolve an import.
If the import is not resolved, then it is saved in @mutUnresolved@,
otherwise the state is updated as needed and the import is discarded. -}
tryImport :: (MName, ImportG PName) -> AllModuleState -> AllModuleState
tryImport (m,i) s =
  case lookupNS NSModule (iModule i) (scopeOf m s) of

    Nothing -> notYet

    Just (One n) ->
      case Map.lookup (ImpNested n) (mutDefs s) of
        Nothing  -> notYet -- needs instantiation
        Just def -> extScopeOf m (interpImportEnv i def) s

    Just (Ambig _) -> s
      {- We ignore names imported through ambiguous modules.
         Later when we do renaming the ambiguity will be reported.
         Note: This means we should report ambiguous names *before*
         undefined names, because some of the undefined names might be due
         to ambiguities. -}

  where
  notYet = s { mutUnresolved = (m,i) : mutUnresolved s }



{- Our main goal here is to determine what is exported by the instantiation,
*NOT* to check if the instantiation is correct (we do this later).  This is
important because it means that we just need to generate fresh names for
the functor definitions, and we don't need to know much about the actual
arguments, which may be instantiations in their own right.

We do wait until the names of the arguments are resolved though, as this
would enable us to implement applicative semantics via caching.

Note that when instantiating a functor, we also need to generate fresh
instances for any submodules of the functor.
-}
tryInstantiate ::
  (MName, Name, Located (ImpName PName), ModuleInstanceArgs PName) ->
  AllModuleState ->
  AllModuleState
tryInstantiate (cm, m, f, args) s =
  case (,) <$> tryLookup scope f <*> tryLookupArgs scope args of
    Nothing -> s { mutUnresolvedInstances = (cm, m, f, args )
                                          : mutUnresolvedInstances s }
    Just (f',args') -> undefined -- instantiateModule m f' args' s
  where
  scope = scopeOf cm s

{- To instantiate M under new name M' in module C

Add { M' } to { mutNesting C }
D  = definition of M

if D is an instantion F A
  then add new instantion target (C,M',F,A)
  else
    do D' = fresh D
       Add { M' = D' } to { mutDefs }
       Let XS = { mutNesting M }
       For X in XS:
          do Let X' fresh equivalent of X
             Instantiate X under new name X' in module M'
-}






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




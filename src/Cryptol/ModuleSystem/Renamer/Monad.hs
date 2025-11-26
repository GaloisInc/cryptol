-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# Language RecordWildCards #-}
{-# Language FlexibleContexts #-}
{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language MultiParamTypeClasses #-}
module Cryptol.ModuleSystem.Renamer.Monad where

import Data.List(sort,foldl')
import           Data.Set(Set)
import qualified Data.Set as Set
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Semigroup as S
import           MonadLib hiding (mapM, mapM_)

import Prelude ()
import Prelude.Compat

import Cryptol.Utils.PP(pp)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(modPathCommon,OrigName(..),OrigSource(..),
                           undefinedModName)
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Binds
import Cryptol.ModuleSystem.Interface
import Cryptol.Parser.AST
import Cryptol.TypeCheck.AST(ModParamNames)
import Cryptol.Parser.Position

import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Renamer.Imports
  (ResolvedLocal,rmodKind,rmodDefines,rmodNested)
import Cryptol.Parser.Name (getNameSource)

-- | Indicates if a name is in a binding poisition or a use site
data NameType = NameBind | NameUse

-- | Information needed to do some renaming.
data RenamerInfo = RenamerInfo
  { renSupply   :: Supply     -- ^ Use to make new names
  , renContext  :: ModPath    -- ^ We are renaming things in here
  , renEnv      :: NamingEnv  -- ^ This is what's in scope
  , renIfaces   :: Map ModName (Either ModParamNames Iface)
    -- ^ External modules
  }

-- The ExceptionT here is for bailing when a fake value like mkFakeName is
-- encountered. These values have already had an error recorded and are being
-- processed for best-effort error reporting so we do not need a value.
newtype RenameM a = RenameM { unRenameM :: ReaderT RO (ExceptionT () (StateT RW Lift)) a }

data RO = RO
  { roLoc       :: Range
  , roNames     :: NamingEnv
  , roExternal  :: Map ModName (Maybe Iface, Map (ImpName Name) (Mod ()))
    -- ^ Externally loaded modules. `Mod` is defined in 'Cryptol.Renamer.Binds'.

  , roCurMod    :: ModPath               -- ^ Current module we are working on

  , roNestedMods :: Map ModPath Name
    {- ^ Maps module paths to the actual name for it.   This is used
         for dependency tracking, to find the name of a containing module.
         See the note on `addDep`. -}

  , roResolvedModules :: Map (ImpName Name) ResolvedLocal
    -- ^ Info about locally defined modules

  , roModParams :: Map Ident RenModParam
    {- ^ Module parameters.  These are used when rename the module parameters,
       and only refer to the parameters of the current module (i.e., no
       outer parameters as those are not needed) -}

  , roFromModParam :: Map Name DepName
    -- ^ Keeps track of which names were introduce by module parameters
    -- and which one.  The `DepName` is always a `ModParamName`.
  }

data RW = RW
  { rwWarnings      :: ![RenamerWarning]
  , rwErrors        :: !(Set RenamerError)
  , rwSupply        :: !Supply
  , rwNameUseCount  :: !(Map Name Int)
    -- ^ How many times did we refer to each name.
    -- Used to generate warnings for unused definitions.

  , rwCurrentDeps     :: Set Name
    -- ^ keeps track of names *used* by something.
    -- see 'depsOf'

  , rwDepGraph        :: Map DepName (Set Name)
    -- ^ keeps track of the dependencies for things.
    -- see 'depsOf'

  , rwExternalDeps  :: !IfaceDecls
    -- ^ Info about imported things, from external modules
  }



data RenModParam = RenModParam
  { renModParamName      :: Ident
  , renModParamRange     :: Range
  , renModParamSig       :: ImpName Name
  , renModParamInstance  :: Map Name Name
    {- ^ Maps names that come into scope through this parameter
         to the names in the *module interface*.
         This is for functors, NOT functor instantantiations. -}
  }




instance S.Semigroup a => S.Semigroup (RenameM a) where
  {-# INLINE (<>) #-}
  a <> b =
    do x <- a
       y <- b
       return (x S.<> y)

instance (S.Semigroup a, Monoid a) => Monoid (RenameM a) where
  {-# INLINE mempty #-}
  mempty = return mempty

  {-# INLINE mappend #-}
  mappend = (S.<>)

instance Functor RenameM where
  {-# INLINE fmap #-}
  fmap f m      = RenameM (fmap f (unRenameM m))

instance Applicative RenameM where
  {-# INLINE pure #-}
  pure x        = RenameM (pure x)

  {-# INLINE (<*>) #-}
  l <*> r       = RenameM (unRenameM l <*> unRenameM r)

instance Monad RenameM where
  {-# INLINE return #-}
  return        = pure

  {-# INLINE (>>=) #-}
  m >>= k       = RenameM (unRenameM m >>= unRenameM . k)

instance FreshM RenameM where
  liftSupply f = RenameM $ sets $ \ RW { .. } ->
    let (a,s') = f rwSupply
        rw'    = RW { rwSupply = s', .. }
     in a `seq` rw' `seq` (a, rw')

instance ExceptionM RenameM () where
  {-# INLINE raise #-}
  raise        = RenameM . raise

runRenamer :: RenamerInfo -> RenameM a
           -> ( Either [RenamerError] (a,Supply)
              , [RenamerWarning]
              )
runRenamer info m = (res, warns)
  where
  warns = sort (rwWarnings rw ++ warnUnused (renContext info) (renEnv info) rw)

  (a,rw) = runM (unRenameM m) ro
                              RW { rwErrors   = Set.empty
                                 , rwWarnings = []
                                 , rwSupply   = renSupply info
                                 , rwNameUseCount = Map.empty
                                 , rwExternalDeps = mempty
                                 , rwCurrentDeps = Set.empty
                                 , rwDepGraph = Map.empty
                                 }

  ro = RO { roLoc   = emptyRange
          , roNames = renEnv info
          , roExternal = Map.mapWithKey toModMap (renIfaces info)
          , roCurMod = renContext info
          , roNestedMods = Map.empty
          , roResolvedModules = mempty
          , roModParams = mempty
          , roFromModParam = mempty
          }

  res | Set.null (rwErrors rw) = case a of
          Left _ -> panic "runRenamer" ["No renaming errors, but no output"]
          Right r -> Right (r,rwSupply rw)
      | otherwise              = Left (Set.toList (rwErrors rw))

  toModMap t ent =
    case ent of
      Left ps -> (Nothing, Map.singleton (ImpTop t) (ifaceSigToMod ps))
      Right i -> (Just i, modToMap (ImpTop t) (ifaceToMod i) mempty)



setCurMod :: ModPath -> RenameM a -> RenameM a
setCurMod mpath (RenameM m) =
  RenameM $ mapReader (\ro -> ro { roCurMod = mpath }) m

getCurMod :: RenameM ModPath
getCurMod = RenameM $ asks roCurMod

getNamingEnv :: RenameM NamingEnv
getNamingEnv = RenameM (asks roNames)

setResolvedLocals :: Map (ImpName Name) ResolvedLocal -> RenameM a -> RenameM a
setResolvedLocals mp (RenameM m) =
  RenameM $ mapReader (\ro -> ro { roResolvedModules = mp }) m

lookupResolved :: ImpName Name -> RenameM ResolvedLocal
lookupResolved nm =
  do mp <- RenameM (roResolvedModules <$> ask)
     case Map.lookup nm mp of
       Just r -> pure r
       Nothing | isFakeName nm -> raise ()
       Nothing ->
         panic
           "lookupResolved"
           ["Missing module: " ++ show nm]

setModParams :: [RenModParam] -> RenameM a -> RenameM a
setModParams ps (RenameM m) =
  do let pmap = Map.fromList [ (renModParamName p, p) | p <- ps ]

         newFrom =
           foldLoop ps mempty \p mp ->
             let nm = ModParamName (renModParamRange p) (renModParamName p)
             in foldLoop (Map.keys (renModParamInstance p)) mp \x ->
                  Map.insert x nm

         upd ro = ro { roModParams    = pmap
                     , roFromModParam = newFrom <> roFromModParam ro
                     }

     RenameM (mapReader upd m)


foldLoop :: [a] -> b -> (a -> b -> b) -> b
foldLoop xs b f = foldl' (flip f) b xs

getModParam :: Ident -> RenameM RenModParam
getModParam p =
  do ps <- RenameM (roModParams <$> ask)
     case Map.lookup p ps of
       Just r  -> pure r
       Nothing -> panic "getModParam" [ "Missing module paramter", show p ]

getNamesFromModParams :: RenameM (Map Name DepName)
getNamesFromModParams = RenameM (roFromModParam <$> ask)

getLocalModParamDeps :: RenameM (Map Ident DepName)
getLocalModParamDeps =
  do ps <- RenameM (roModParams <$> ask)
     let toName mp = ModParamName (renModParamRange mp) (renModParamName mp)
     pure (toName <$> ps)


setNestedModule :: Map ModPath Name -> RenameM a -> RenameM a
setNestedModule mp (RenameM m) =
  RenameM $ mapReader (\ro -> ro { roNestedMods = mp }) m

nestedModuleOrig :: ModPath -> RenameM (Maybe Name)
nestedModuleOrig x = RenameM (asks (Map.lookup x . roNestedMods))


-- | Record an error.
recordError :: RenamerError -> RenameM ()
recordError f = RenameM $
  do RW { .. } <- get
     set RW { rwErrors = Set.insert f rwErrors, .. }

recordWarning :: RenamerWarning -> RenameM ()
recordWarning w =
  RenameM $ sets_ \rw -> rw { rwWarnings = w : rwWarnings rw }

collectIfaceDeps :: RenameM a -> RenameM (IfaceDecls,a)
collectIfaceDeps (RenameM m) =
  RenameM
  do ds  <- sets \s -> (rwExternalDeps s, s { rwExternalDeps = mempty })
     a   <- m
     ds' <- sets \s -> (rwExternalDeps s, s { rwExternalDeps = ds })
     pure (ds',a)

-- |  Rename something.  All name uses in the sub-computation are assumed
-- to be dependenices of the thing.
depsOf :: DepName -> RenameM a -> RenameM a
depsOf x (RenameM m) = RenameM
  do ds <- sets \rw -> (rwCurrentDeps rw, rw { rwCurrentDeps = Set.empty })
     a  <- m
     sets_ \rw ->
        rw { rwCurrentDeps = Set.union (rwCurrentDeps rw) ds
           , rwDepGraph = Map.insert x (rwCurrentDeps rw) (rwDepGraph rw)
           }
     pure a

-- | This is used when renaming a group of things.  The result contains
-- dependencies between names defined in the group, and is intended to
-- be used to order the group members in dependency order.
depGroup :: RenameM a -> RenameM (a, Map DepName (Set Name))
depGroup (RenameM m) = RenameM
  do ds  <- sets \rw -> (rwDepGraph rw, rw { rwDepGraph = Map.empty })
     a   <- m
     ds1 <- sets \rw -> (rwDepGraph rw, rw { rwDepGraph = ds })
     pure (a,ds1)

-- | Get the source range for wahtever we are currently renaming.
curLoc :: RenameM Range
curLoc  = RenameM (roLoc `fmap` ask)

-- | Annotate something with the current range.
located :: a -> RenameM (Located a)
located thing =
  do srcRange <- curLoc
     return Located { .. }

-- | Do the given computation using the source code range from `loc` if any.
withLoc :: HasLoc loc => loc -> RenameM a -> RenameM a
withLoc loc m = RenameM $ case getLoc loc of

  Just range -> do
    ro <- ask
    local ro { roLoc = range } (unRenameM m)

  Nothing -> unRenameM m


-- | Shadow the current naming environment with some more names.
shadowNames :: BindsNames env => env -> RenameM a -> RenameM a
shadowNames  = shadowNames' CheckAll

data EnvCheck = CheckAll     -- ^ Check for overlap and shadowing
              | CheckOverlap -- ^ Only check for overlap
              | CheckNone    -- ^ Don't check the environment
                deriving (Eq,Show)

-- | Report errors if the given naming environemnt contains multiple
-- definitions for the same symbol
checkOverlap :: NamingEnv -> RenameM NamingEnv
checkOverlap env =
  case findAmbig env of
    []    -> pure env
    ambig -> do mapM_ recordError [ OverlappingSyms xs | xs <- ambig ]
                pure (forceUnambig env)

-- | Issue warnings if entries in the first environment would
--   shadow something in the second. This warning is only emited 
--   for UserNames
checkShadowing :: NamingEnv -> NamingEnv -> RenameM ()
checkShadowing envNew envOld =
  mapM_ recordWarning
    [ SymbolShadowed p x xs | (p,x,xs) <- findShadowing envNew envOld, checkSystemName p x]
      where
        checkSystemName p' x' = getNameSource p' /= Just SystemName && nameSrc x' /= SystemName


-- | Shadow the current naming environment with some more names.
-- XXX: The checks are really confusing
shadowNames' :: BindsNames env => EnvCheck -> env -> RenameM a -> RenameM a
shadowNames' check names m = do
  do env    <- liftSupply (defsOf names)
     envOld <- RenameM (roNames <$> ask)
     env1   <- case check of
                 CheckNone    -> pure env
                 CheckOverlap -> checkOverlap env
                 CheckAll     -> do checkShadowing env envOld
                                    checkOverlap env
     RenameM
       do ro  <- ask
          let ro' = ro { roNames = env1 `shadowing` envOld }
          local ro' (unRenameM m)

recordUse :: Name -> RenameM ()
recordUse x = RenameM $ sets_ $ \rw ->
  rw { rwNameUseCount = Map.insertWith (+) x 1 (rwNameUseCount rw) }
  {- NOTE: we don't distinguish between bindings and uses here, because
  the situation is complicated by the pattern signatures where the first
  "use" site is actually the binding site.  Instead we just count them all, and
  something is considered unused if it is used only once (i.e, just the
  binding site) -}

-- | Mark something as a dependency. This is similar but different from
-- `recordUse`, in particular:
--    * We only record use sites, not bindings
--    * We record all namespaces, not just types
--    * We only keep track of actual uses mentioned in the code.
--      Otoh, `recordUse` also considers exported entities to be used.
--    * If we depend on a name from a sibling submodule we add a dependency on
--      the module in our common ancestor.  Examples:
--      - @A::B::x@ depends on @A::B::C::D::y@, @x@ depends on @A::B::C@
--      - @A::B::x@ depends on @A::P::Q::y@@,   @x@ depends on @A::P@

addDep :: Name -> RenameM ()
addDep x =
  do cur  <- getCurMod
     deps <- case nameInfo x of
               GlobalName _ OrigName { ogModule = m }
                 | Just (c,_,i:_) <- modPathCommon cur m ->
                 do mb <- nestedModuleOrig (Nested c i)
                    pure case mb of
                           Just y  -> Set.fromList [x,y]
                           Nothing -> Set.singleton x
               _ -> pure (Set.singleton x)
     RenameM $
       sets_ \rw -> rw { rwCurrentDeps = Set.union deps (rwCurrentDeps rw) }


warnUnused :: ModPath -> NamingEnv -> RW -> [RenamerWarning]
warnUnused m0 env rw =
  map UnusedName
  $ Map.keys
  $ Map.filterWithKey keep
  $ rwNameUseCount rw
  where
  keep nm count = count == 1 && isLocal nm
  oldNames = Map.findWithDefault Set.empty NSType (visibleNames env)

  -- returns true iff the name comes from a definition in a nested module,
  -- including the current module
  isNestd og = case modPathCommon m0 (ogModule og) of
                 Just (_,[],_) | FromDefinition <- ogSource og -> True
                 _ -> False

  isLocal nm = case nameInfo nm of
                 GlobalName sys og ->
                   sys == UserName && isNestd og && nm `Set.notMember` oldNames
                 LocalName {} -> True


getExternal :: RenameM (ImpName Name -> Mod ())
getExternal =
  do mp <- roExternal <$> RenameM ask
     pure \nm -> let mb = do t   <- case nm of
                                      ImpTop t  -> pure t
                                      ImpNested x -> nameTopModuleMaybe x
                             (_,mp1) <- Map.lookup t mp
                             Map.lookup nm mp1
                 in case mb of
                      Just m -> m
                      Nothing -> panic "getExternal"
                                    ["Missing external name", show (pp nm) ]

getExternalMod :: ImpName Name -> RenameM (Mod ())
getExternalMod nm = ($ nm) <$> getExternal

-- | Returns `Nothing` if the name does not refer to a module (i.e., it is a sig)
getTopModuleIface :: ImpName Name -> RenameM (Maybe Iface)
getTopModuleIface nm =
  do mp <- roExternal <$> RenameM ask
     let t = case nm of
               ImpTop t' -> t'
               ImpNested x -> nameTopModule x
     case Map.lookup t mp of
       Just (mb, _) -> pure mb
       Nothing -> panic "getTopModuleIface"
                                ["Missing external module", show (pp nm) ]

{- | Record an import:
      * record external dependency if the name refers to an external import
      * record an error if the imported thing is a functor
-}
recordImport :: Range -> ImpName Name -> RenameM ()
recordImport r i =
  do ro <- RenameM ask
     case Map.lookup i (roResolvedModules ro) of
       Just loc ->
         case rmodKind loc of
           AModule -> pure ()
           k       -> recordError (ModuleKindMismatch r i AModule k)
       Nothing ->
        do mb <- getTopModuleIface i
           case mb of
             Nothing -> recordError (ModuleKindMismatch r i AModule ASignature)
             Just iface
               | ifaceIsFunctor iface ->
                       recordError (ModuleKindMismatch r i AModule AFunctor)
               | otherwise ->
                 RenameM $ sets_ \s -> s { rwExternalDeps = ifDefines iface <>
                                                            rwExternalDeps s }


-- | Lookup a name either in the locally resolved thing or in an external module
lookupModuleThing :: ImpName Name -> RenameM (Either ResolvedLocal (Mod ()))
lookupModuleThing nm =
  do ro <- RenameM ask
     case Map.lookup nm (roResolvedModules ro) of
       Just loc -> pure (Left loc)
       Nothing  -> Right <$> getExternalMod nm

lookupDefines :: ImpName Name -> RenameM NamingEnv
lookupDefines nm =
  do thing <- lookupModuleThing nm
     pure case thing of
            Left loc -> rmodDefines loc
            Right e  -> modDefines e

checkIsModule :: Range -> ImpName Name -> ModKind -> RenameM ()
checkIsModule r nm expect =
  do thing <- lookupModuleThing nm
     let actual = case thing of
                    Left rmod -> rmodKind rmod
                    Right mo  -> modKind mo
     unless (actual == expect)
        (recordError (ModuleKindMismatch r nm expect actual))

lookupDefinesAndSubs :: ImpName Name -> RenameM (NamingEnv, Set Name)
lookupDefinesAndSubs nm =
  do thing <- lookupModuleThing nm
     pure case thing of
            Left rmod -> ( rmodDefines rmod, rmodNested rmod)
            Right m ->
              ( modDefines m
              , Set.unions [ Map.keysSet (modMods m)
                           , Map.keysSet (modInstances m)
                           ]
              )

isFakeName :: ImpName Name -> Bool
isFakeName m =
  case m of
    ImpTop x -> x == undefinedModName
    ImpNested x ->
      case nameTopModuleMaybe x of
        Just y  -> y == undefinedModName
        Nothing -> False

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
module Cryptol.ModuleSystem.Renamer.Monad where

import Data.List(sort)
import           Data.Set(Set)
import qualified Data.Set as Set
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Semigroup as S
import           MonadLib hiding (mapM, mapM_)

import Prelude ()
import Prelude.Compat

import Cryptol.Utils.Panic(panic)
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Binds
import Cryptol.ModuleSystem.Interface
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Utils.Ident(modPathCommon,OrigName(..))

import Cryptol.ModuleSystem.Renamer.Error

-- | Indicates if a name is in a binding poisition or a use site
data NameType = NameBind | NameUse

-- | Information needed to do some renaming.
data RenamerInfo = RenamerInfo
  { renSupply   :: Supply     -- ^ Use to make new names
  , renContext  :: ModPath    -- ^ We are renaming things in here
  , renEnv      :: NamingEnv  -- ^ This is what's in scope
  , renIfaces   :: ModName -> Iface
  }

newtype RenameM a = RenameM { unRenameM :: ReaderT RO (StateT RW Lift) a }

data RO = RO
  { roLoc    :: Range
  , roNames  :: NamingEnv
  , roIfaces :: ModName -> Iface
  , roCurMod :: ModPath           -- ^ Current module we are working on
  , roNestedMods :: Map ModPath Name
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
    -- ^ Info about imported things
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
  return x      = RenameM (return x)

  {-# INLINE (>>=) #-}
  m >>= k       = RenameM (unRenameM m >>= unRenameM . k)

instance FreshM RenameM where
  liftSupply f = RenameM $ sets $ \ RW { .. } ->
    let (a,s') = f rwSupply
        rw'    = RW { rwSupply = s', .. }
     in a `seq` rw' `seq` (a, rw')


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
          , roIfaces = renIfaces info
          , roCurMod = renContext info
          , roNestedMods = Map.empty
          }

  res | Set.null (rwErrors rw) = Right (a,rwSupply rw)
      | otherwise              = Left (Set.toList (rwErrors rw))


setCurMod :: ModPath -> RenameM a -> RenameM a
setCurMod mpath (RenameM m) =
  RenameM $ mapReader (\ro -> ro { roCurMod = mpath }) m

getCurMod :: RenameM ModPath
getCurMod = RenameM $ asks roCurMod

getNamingEnv :: RenameM NamingEnv
getNamingEnv = RenameM (asks roNames)


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
-- dependencies between names defines and the group, and is intended to
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
-- shadow something in the second.
checkShadowing :: NamingEnv -> NamingEnv -> RenameM ()
checkShadowing envNew envOld =
  mapM_ recordWarning
    [ SymbolShadowed p x xs | (p,x,xs) <- findShadowing envNew envOld ]


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
  map warn
  $ Map.keys
  $ Map.filterWithKey keep
  $ rwNameUseCount rw
  where
  warn x   = UnusedName x
  keep nm count = count == 1 && isLocal nm
  oldNames = Map.findWithDefault Set.empty NSType (visibleNames env)
  isLocal nm = case nameInfo nm of
                 GlobalName sys OrigName { ogModule = m } ->
                   sys == UserName && m == m0 && nm `Set.notMember` oldNames
                 LocalName {} -> True

-- | Get the exported declarations in a module
lookupImport :: Import -> RenameM IfaceDecls
lookupImport imp = RenameM $
  do getIf <- roIfaces <$> ask
     let ifs = ifPublic (getIf (iModule imp))
     sets_ \s -> s { rwExternalDeps = ifs <> rwExternalDeps s }
     pure ifs

-- XXX: Maybe we'd want to cache some of the conversion to Mod?
getLoadedMods :: RenameM (ImpName Name -> Mod ())
getLoadedMods =
  do getIf <- RenameM (roIfaces <$> ask)
     pure \nm ->
      case nm of
        ImpTop m -> ifaceToMod (getIf m)
        ImpNested n ->
          let top = nameTopModule n
              mp = modToMap (ImpTop top) (ifaceToMod (getIf top)) Map.empty
          in case Map.lookup nm mp of
               Just m  -> m
               Nothing -> panic "lookupImportMod"
                            [ "Missing nested module", show nm ]







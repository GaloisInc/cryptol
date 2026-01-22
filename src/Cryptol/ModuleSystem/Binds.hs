{-# Language BlockArguments #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
module Cryptol.ModuleSystem.Binds
  ( BindsNames
  , TopDef(..)
  , Mod(..)
  , ModKind(..)
  , modNested
  , modBuilder
  , topModuleDefs
  , topDeclsDefs
  , newModParam
  , newFunctorInst
  , InModule(..)
  , ifaceToMod
  , ifaceSigToMod
  , modToMap
  , defsOf
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Control.Monad(foldM,forM)
import qualified MonadLib as M

import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident(allNamespaces)
import Cryptol.Parser.Position
import Cryptol.Parser.Name(isSystemName)
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Exports(exportedDecls,exported)
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.TypeCheck.Type(ModParamNames(..))



data TopDef = TopMod ModName (Mod ())
            | TopInst ModName (ImpName PName) (ModuleInstanceArgs PName)

-- | Things defined by a module
data Mod a = Mod
  { modImports   :: [ ImportG (ImpName PName) ]
  , modKind      :: ModKind
  , modInstances :: Map Name (ImpName PName, ModuleInstanceArgs PName)
  , modMods      :: Map Name (Mod a) -- ^ this includes signatures

  , modDefines   :: NamingEnv
    {- ^ Things defined by this module.  Note the for normal modules we
    really just need the public names, however for things within
    functors we need all defined names, so that we can generate fresh
    names in instantiations -}

  , modPublic    :: !(Set Name)
    -- ^ These are the exported names

  , modState     :: a
    {- ^ Used in the import loop to track the current state of processing.
         The reason this is here, rather than just having a pair in the
         other algorithm is because this type is recursive (for nested modules)
         and it is conveninet to keep track for all modules at once -}
  }

modNested :: Mod a -> Set Name
modNested m = Set.unions [ Map.keysSet (modInstances m)
                         , Map.keysSet (modMods m)
                         ]

instance Functor Mod where
  fmap f m = m { modState = f (modState m)
               , modMods  = fmap f <$> modMods m
               }

-- | Generate a map from this module and all modules nested in it.
modToMap ::
  ImpName Name -> Mod () ->
  Map (ImpName Name) (Mod ()) -> Map (ImpName Name) (Mod ())
modToMap x m mp = Map.insert x m (Map.foldrWithKey add mp (modMods m))
  where
  add n = modToMap (ImpNested n)

-- | Make a `Mod` from the public declarations in an interface.
-- This is used to handle imports.
ifaceToMod :: IfaceG name -> Mod ()
ifaceToMod iface = ifaceNamesToMod iface (ifaceIsFunctor iface) (ifNames iface)

ifaceNamesToMod :: IfaceG topname -> Bool -> IfaceNames name -> Mod ()
ifaceNamesToMod iface params names =
  Mod
    { modKind    = if params then AFunctor else AModule
    , modMods    = (ifaceNamesToMod iface False <$> ifModules decls)
                   `Map.union`
                   (ifaceToMod <$> ifFunctors decls)
                   `Map.union`
                   (ifaceSigToMod <$> ifSignatures decls)
    , modDefines = namingEnvFromNames defs
    , modPublic  = ifsPublic names

    , modImports   = []
    , modInstances = mempty
    , modState     = ()
    }
  where
  defs      = ifsDefines names
  isLocal x = x `Set.member` defs
  decls     = filterIfaceDecls isLocal (ifDefines iface)


ifaceSigToMod :: ModParamNames -> Mod ()
ifaceSigToMod ps = Mod
  { modImports   = []
  , modKind      = ASignature
  , modInstances = mempty
  , modMods      = mempty
  , modDefines   = env
  , modPublic    = namingEnvNames env
  , modState     = ()
  }
  where
  env = modParamNamesNamingEnv ps






type ModBuilder = SupplyT (M.StateT [RenamerError] M.Id)

modBuilder :: ModBuilder a -> Supply -> ((a, [RenamerError]),Supply)
modBuilder m s = ((a,errs),s1)
  where ((a,s1),errs) = M.runId (M.runStateT [] (runSupplyT s m))

defErr :: RenamerError -> ModBuilder ()
defErr a = M.lift (M.sets_ (a:))

defNames :: BuildNamingEnv -> ModBuilder NamingEnv
defNames b = liftSupply \s -> M.runId (runSupplyT s (runBuild b))


topModuleDefs :: Module PName -> ModBuilder TopDef
topModuleDefs m =
  case mDef m of
    NormalModule ds -> TopMod mname <$> declsToMod (Just (TopModule mname)) ds
    FunctorInstance f as _ -> pure (TopInst mname (thing f) as)
    InterfaceModule s -> TopMod mname <$> sigToMod (TopModule mname) s
  where
  mname = thing (mName m)

topDeclsDefs :: ModPath -> [TopDecl PName] -> ModBuilder (Mod ())
topDeclsDefs = declsToMod . Just

sigToMod :: ModPath -> Signature PName -> ModBuilder (Mod ())
sigToMod mp sig =
  do env <- defNames (signatureDefs mp sig)
     pure Mod { modImports   = map thing (sigImports sig)
              , modKind      = ASignature
              , modInstances = mempty
              , modMods      = mempty
              , modDefines   = env
              , modPublic    = namingEnvNames env
              , modState     = ()
              }



declsToMod :: Maybe ModPath -> [TopDecl PName] -> ModBuilder (Mod ())
declsToMod mbPath ds =
  do defs <- defNames (foldMap (namingEnv . InModule mbPath) ds)
     let expSpec = exportedDecls ds
     let pub     = Set.fromList
                     [ name
                     | ns    <- allNamespaces
                     , pname <- Set.toList (exported ns expSpec)
                     , name  <- lookupListNS ns pname defs
                     ]

     case findAmbig defs of
       bad@(_ : _) : _ ->
         -- defErr (MultipleDefinitions mbPath (nameIdent f) (map nameLoc bad))
         defErr (OverlappingSyms bad)
       _ -> pure ()

     let mo = Mod { modImports      = [ thing i | DImport i <- ds ]
                  , modKind         = if any isParamDecl ds
                                         then AFunctor else AModule
                  , modInstances    = mempty
                  , modMods         = mempty
                  , modDefines      = defs
                  , modPublic       = pub
                  , modState        = ()
                  }

     foldM (checkNest defs) mo ds

  where
  checkNest defs mo d =
    case d of
      DModule tl ->
        do let NestedModule nmod = tlValue tl
               pname = thing (mName nmod)
               name  = case lookupNS NSModule pname defs of
                         Just xs -> anyOne xs
                         _ -> panic "declsToMod" ["undefined name", show pname]
           case mbPath of
             Nothing ->
               do defErr (UnexpectedNest (srcRange (mName nmod)) pname)
                  pure mo
             Just path ->
                case mDef nmod of

                   NormalModule xs ->
                     do m <- declsToMod (Just (Nested path (nameIdent name))) xs
                        pure mo { modMods = Map.insert name m (modMods mo) }

                   FunctorInstance f args _ ->
                      pure mo { modInstances = Map.insert name (thing f, args)
                                                    (modInstances mo) }

                   InterfaceModule sig ->
                      do m <- sigToMod (Nested path (nameIdent name)) sig
                         pure mo { modMods = Map.insert name m (modMods mo) }


      _ -> pure mo



-- | These are the names "owned" by the signature.  These names are
-- used when resolving the signature.  They are also used to figure out what
-- names to instantuate when the signature is used.
signatureDefs :: ModPath -> Signature PName -> BuildNamingEnv
signatureDefs m sig =
     mconcat [ namingEnv (InModule loc p) | p <- sigTypeParams sig ]
  <> mconcat [ namingEnv (InModule loc p) | p <- sigFunParams sig ]
  <> mconcat [ namingEnv (InModule loc p) | p <- sigDecls sig ]
  where
  loc = Just m
--------------------------------------------------------------------------------




--------------------------------------------------------------------------------
-- Computes the names introduced by various declarations.

-- | Things that define exported names.
class BindsNames a where
  namingEnv :: a -> BuildNamingEnv

newtype BuildNamingEnv = BuildNamingEnv { runBuild :: SupplyT M.Id NamingEnv }

buildNamingEnv :: BuildNamingEnv -> Supply -> (NamingEnv,Supply)
buildNamingEnv b supply = M.runId $ runSupplyT supply $ runBuild b

-- | Generate a 'NamingEnv' using an explicit supply.
defsOf :: BindsNames a => a -> Supply -> (NamingEnv,Supply)
defsOf = buildNamingEnv . namingEnv

instance Semigroup BuildNamingEnv where
  BuildNamingEnv a <> BuildNamingEnv b = BuildNamingEnv $
    do x <- a
       y <- b
       return (mappend x y)

instance Monoid BuildNamingEnv where
  mempty = BuildNamingEnv (pure mempty)

  mappend = (<>)

  mconcat bs = BuildNamingEnv $
    do ns <- sequence (map runBuild bs)
       return (mconcat ns)

instance BindsNames NamingEnv where
  namingEnv env = BuildNamingEnv (return env)
  {-# INLINE namingEnv #-}

instance BindsNames a => BindsNames (Maybe a) where
  namingEnv = foldMap namingEnv
  {-# INLINE namingEnv #-}

instance BindsNames a => BindsNames [a] where
  namingEnv = foldMap namingEnv
  {-# INLINE namingEnv #-}

-- | Generate a type renaming environment from the parameters that are bound by
-- this schema.
instance BindsNames (Schema PName) where
  namingEnv (Forall ps _ _ _) = foldMap namingEnv ps
  {-# INLINE namingEnv #-}



-- | Introduce the name
instance BindsNames (InModule (Bind PName)) where
  namingEnv (InModule mb b) = BuildNamingEnv $
    do let Located { .. } = bName b
       n <- case mb of
              Just m  -> newTop NSValue m thing (bFixity b) srcRange
              Nothing -> newLocal NSValue thing srcRange -- local fixitiies?

       return (singletonNS NSValue thing n)

-- | Generate the naming environment for a type parameter.
instance BindsNames (TParam PName) where
  namingEnv TParam { .. } = BuildNamingEnv $
    do let range = fromMaybe emptyRange tpRange
       n <- newLocal NSType tpName range
       return (singletonNS NSType tpName n)


instance BindsNames (InModule (TopDecl PName)) where
  namingEnv (InModule ns td) =
    case td of
      Decl d           -> namingEnv (InModule ns (tlValue d))
      DPrimType d      -> namingEnv (InModule ns (tlValue d))
      TDNewtype d      -> namingEnv (InModule ns (tlValue d))
      TDEnum d         -> namingEnv (InModule ns (tlValue d))
      DParamDecl {}    -> mempty
      Include {}       -> mempty
      DImport {}       -> mempty -- see 'openLoop' in the renamer
      DModule m        -> namingEnv (InModule ns (tlValue m))
      DModParam {}     -> mempty -- shouldn't happen
      DInterfaceConstraint {} -> mempty
        -- handled in the renamer as we need to resolve
        -- the signature name first (similar to import)


instance BindsNames (InModule (NestedModule PName)) where
  namingEnv (InModule ~(Just m) (NestedModule mdef)) = BuildNamingEnv $
    do let pnmame = mName mdef
       nm   <- newTop NSModule m (thing pnmame) Nothing (srcRange pnmame)
       pure (singletonNS NSModule (thing pnmame) nm)

instance BindsNames (InModule (PrimType PName)) where
  namingEnv (InModule ~(Just m) PrimType { .. }) =
    BuildNamingEnv $
      do let Located { .. } = primTName
         nm <- newTop NSType m thing primTFixity srcRange
         pure (singletonNS NSType thing nm)

instance BindsNames (InModule (ParameterFun PName)) where
  namingEnv (InModule ~(Just ns) ParameterFun { .. }) = BuildNamingEnv $
    do let Located { .. } = pfName
       ntName <- newTop NSValue ns thing pfFixity srcRange
       return (singletonNS NSValue thing ntName)

instance BindsNames (InModule (ParameterType PName)) where
  namingEnv (InModule ~(Just ns) ParameterType { .. }) = BuildNamingEnv $
    -- XXX: we don't seem to have a fixity environment at the type level
    do let Located { .. } = ptName
       ntName <- newTop NSType ns thing Nothing srcRange
       return (singletonNS NSType thing ntName)

instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ~(Just ns) Newtype { .. }) = BuildNamingEnv $
    do let Located { .. } = nName
       ntName    <- newTop NSType  ns thing Nothing srcRange
       ntConName <- newTop NSConstructor ns thing Nothing srcRange
       return (singletonNS NSType thing ntName `mappend`
               singletonNS NSConstructor thing ntConName)

instance BindsNames (InModule (EnumDecl PName)) where
  namingEnv (InModule (Just ns) EnumDecl { .. }) = BuildNamingEnv $
    do enName   <- newTop NSType ns (thing eName) Nothing (srcRange eName)
       conNames <- forM eCons \topc ->
                      do let c     = ecName (tlValue topc)
                             pname = thing c
                         cName <- newTop NSConstructor ns pname Nothing
                                                                  (srcRange c)
                         pure (singletonNS NSConstructor pname cName)
       pure (mconcat (singletonNS NSType (thing eName) enName : conNames))
  namingEnv _ = panic "namingEnv" ["Unreachable"]

-- | The naming environment for a single declaration.
instance BindsNames (InModule (Decl PName)) where
  namingEnv (InModule pfx d) = case d of
    DBind b                 -> namingEnv (InModule pfx b)
    DSignature ns _sig      -> foldMap qualBind ns
    DPragma ns _p           -> foldMap qualBind ns
    DType syn               -> qualType (tsName syn) (tsFixity syn)
    DProp syn               -> qualType (psName syn) (psFixity syn)
    DLocated d' _           -> namingEnv (InModule pfx d')
    DRec {}                 -> panic "namingEnv" [ "DRec" ]
    DPatBind _pat _e        -> panic "namingEnv" ["Unexpected pattern binding"]
    DFixity{}               -> panic "namingEnv" ["Unexpected fixity declaration"]

    where

    mkName ns ln fx = case pfx of
                        Just m  -> newTop ns m (thing ln) fx (srcRange ln)
                        Nothing -> newLocal ns (thing ln) (srcRange ln)

    qualBind ln = BuildNamingEnv $
      do n <- mkName NSValue ln Nothing
         return (singletonNS NSValue (thing ln) n)

    qualType ln f = BuildNamingEnv $
      do n <- mkName NSType ln f
         return (singletonNS NSType (thing ln) n)

instance BindsNames (InModule (SigDecl PName)) where
  namingEnv (InModule m d) =
    case d of
      SigTySyn ts _    -> namingEnv (InModule m (DType ts))
      SigPropSyn ps _  -> namingEnv (InModule m (DProp ps))

instance BindsNames (Pattern PName) where
  namingEnv pat =
    case pat of
      PVar x -> BuildNamingEnv (
        do y <- newLocal NSValue (thing x) (srcRange x)
           pure (singletonNS NSValue (thing x) y)
        )
      PCon _ xs     -> mconcat (map namingEnv xs)
      PLocated p _r -> namingEnv p
      PTyped p _t   -> namingEnv p
      _ -> panic "namingEnv" ["Unexpected pattern"]



--------------------------------------------------------------------------------
-- Helpers

newTop ::
  FreshM m => Namespace -> ModPath -> PName -> Maybe Fixity -> Range -> m Name
newTop ns m thing fx rng =
  liftSupply (mkDeclared ns m src (getIdent thing) fx rng)
  where src = if isSystemName thing then SystemName else UserName

newLocal :: FreshM m => Namespace -> PName -> Range -> m Name
newLocal ns thing rng = liftSupply (mkLocalPName ns thing rng)

-- | Given a name in a signature, make a name for the parameter corresponding
-- to the signature.
newModParam :: FreshM m => ModPath -> Ident -> Range -> Name -> m Name
newModParam m i rng n = liftSupply (mkModParam m i rng n)

-- | Given a name in a functor, make a fresh name for the corresponding thing in
-- the instantiation.
--
-- The 'ModPath' should be the instantiation not the functor.
newFunctorInst :: FreshM m => ModPath -> Name -> m Name
newFunctorInst m n = liftSupply (freshNameFor m n)


{- | Do something in the context of a module.
If `Nothing` than we are working with a local declaration.
Otherwise we are at the top-level of the given module.

By wrapping types with this, we can pass the module path
to methods that need the extra information. -}
data InModule a = InModule (Maybe ModPath) a
                  deriving (Functor,Traversable,Foldable,Show)




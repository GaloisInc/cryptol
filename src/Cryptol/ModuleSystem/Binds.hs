{-# Language BlockArguments #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Cryptol.ModuleSystem.Binds
  ( BindsNames
  , TopDef(..)
  , Mod(..)
  , modNested
  , modBuilder
  , topModuleDefs
  , topDeclsDefs
  , interpImportIface
  , newModParam
  , InModule(..)
  , ifaceToMod
  , modToMap
  , defsOf
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Control.Monad(foldM)
import qualified MonadLib as M

import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident(allNamespaces)
import Cryptol.Parser.Position
import Cryptol.Parser.Name(isGeneratedName)
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Exports(exportedDecls,exported)
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface



data TopDef = TopMod ModName (Mod ())
            | TopInst ModName (ImpName PName) (ModuleInstanceArgs PName)
            | TopInstOld ModName ModName (Mod ())

-- | Things defined by a module
data Mod a = Mod
  { modImports   :: [ ImportG (ImpName PName) ]
  , modParams    :: Bool -- True = has params
  , modInstances :: Map Name (ImpName PName, ModuleInstanceArgs PName)
  , modMods      :: Map Name (Mod a)
  , modSigs      :: Map Name NamingEnv
  , modDefines   :: NamingEnv  -- ^ Things defined by this module
  , modPublic    :: !(Set Name)   -- ^ These are the exported names

  , modState     :: a
    {- ^ Used in the import loop to track the current state of processing.
         The reason this is here, rather than just having a pair in the
         other algorithm is because this type is recursive (for nested modules)
         and it is conveninet to keep track for all modules at once -}
  }

modNested :: Mod a -> Set Name
modNested m = Set.unions [ Map.keysSet (modInstances m)
                         , Map.keysSet (modSigs m)
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
ifaceToMod iface =
  Mod
    { modImports    = []
    , modParams     = case ifParams iface of
                        Nothing -> False
                        Just {} -> True
    , modInstances  = undefined
    , modMods       = ifaceToMod         <$> ifModules pub
    , modSigs       = modParamsNamingEnv <$> ifSignatures pub
    , modDefines    = defs
    , modPublic     = namingEnvNames defs
    , modState      = ()
    }
  where
  pub = ifPublic iface
  defs = unqualifiedEnv pub


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
    FunctorInstanceOld f ds ->
      TopInstOld mname (thing f) <$> declsToMod Nothing ds
    FunctorInstance f as _ ->
      pure (TopInst mname (thing f) as)

  where
  mname = thing (mName m)

topDeclsDefs :: [TopDecl PName] -> ModBuilder (Mod ())
topDeclsDefs = declsToMod Nothing


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
                  , modParams       = any isParamDecl ds
                  , modInstances    = mempty
                  , modMods         = mempty
                  , modSigs         = mempty
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
                   FunctorInstanceOld {} ->
                     do defErr (UnexpectedNest (srcRange (mName nmod)) pname)
                        pure mo
                   FunctorInstance f args _ ->
                      pure mo { modInstances = Map.insert name (thing f, args)
                                                    (modInstances mo) }

      DModSig tl ->
        do let sig   = tlValue tl
               pname = thing (sigName sig)
               name  = case lookupNS NSSignature pname defs of
                         Just (One x) -> x
                         _ -> panic "declsToMod" ["sig: Missed ambig/undefined"]
           case mbPath of
             {- No top level signatures at the moment, as nothing would
                be in scope in them (they don't have imports) -}
             Nothing ->
               do defErr (UnexpectedNest (srcRange (sigName sig)) pname)
                  pure mo
             Just path ->
                do newEnv <-
                     defNames (signatureDefs (Nested path (nameIdent name)) sig)
                   pure mo { modSigs = Map.insert name newEnv (modSigs mo) }

      _ -> pure mo



-- | These are the names "owned" by the signature.  These names are
-- used when resolving the signature.  They are also used to figure out what
-- names to instantuate when the signature is used.
signatureDefs :: ModPath -> Signature PName -> BuildNamingEnv
signatureDefs m sig =
     mconcat [ namingEnv (InModule loc p) | p <- sigTypeParams sig ]
  <> mconcat [ namingEnv (InModule loc p) | p <- sigFunParams sig ]
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




-- | Interpret an import in the context of an interface, to produce a name
-- environment for the renamer, and a 'NameDisp' for pretty-printing.
interpImportIface :: Import     {- ^ The import declarations -} ->
                IfaceDecls {- ^ Declarations of imported module -} ->
                NamingEnv
interpImportIface imp = interpImportEnv imp . unqualifiedEnv



data ImportIface = ImportIface Import Iface

-- | Produce a naming environment from an interface file, that contains a
-- mapping only from unqualified names to qualified ones.
instance BindsNames ImportIface where
  namingEnv (ImportIface imp Iface { .. }) = BuildNamingEnv $
    return (interpImportIface imp ifPublic)
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
      DParameterType d -> namingEnv (InModule ns d)
      DParameterConstraint {} -> mempty
      DParameterFun  d -> namingEnv (InModule ns d)
      Include _        -> mempty
      DImport {}       -> mempty -- see 'openLoop' in the renamer
      DModule m        -> namingEnv (InModule ns (tlValue m))

      DModSig s        -> namingEnv (InModule ns (tlValue s))
      DModParam {}     -> mempty-- handled in the renamer as we need to resolve
                                 -- the signature name first (similar to import)

instance BindsNames (InModule (NestedModule PName)) where
  namingEnv (InModule ~(Just m) (NestedModule mdef)) = BuildNamingEnv $
    do let pnmame = mName mdef
       nm   <- newTop NSModule m (thing pnmame) Nothing (srcRange pnmame)
       pure (singletonNS NSModule (thing pnmame) nm)

instance BindsNames (InModule (Signature PName)) where
  namingEnv (InModule ~(Just m) sig) = BuildNamingEnv
    do let pname = sigName sig
       nm <- newTop NSSignature m (thing pname) Nothing (srcRange pname)
       pure (singletonNS NSSignature (thing pname) nm)



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

-- NOTE: we use the same name at the type and expression level, as there's only
-- ever one name introduced in the declaration. The names are only ever used in
-- different namespaces, so there's no ambiguity.
instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ~(Just ns) Newtype { .. }) = BuildNamingEnv $
    do let Located { .. } = nName
       ntName <- newTop NSType ns thing Nothing srcRange
       -- XXX: the name reuse here is sketchy
       return (singletonNS NSType thing ntName `mappend` singletonNS NSValue thing ntName)

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



--------------------------------------------------------------------------------
-- Helpers

newTop ::
  FreshM m => Namespace -> ModPath -> PName -> Maybe Fixity -> Range -> m Name
newTop ns m thing fx rng =
  liftSupply (mkDeclared ns m src (getIdent thing) fx rng)
  where src = if isGeneratedName thing then SystemName else UserName

newLocal :: FreshM m => Namespace -> PName -> Range -> m Name
newLocal ns thing rng = liftSupply (mkLocal ns (getIdent thing) rng)

-- | Given a name in a signature, make a name for the parameter corresponding
-- to the signature.
newModParam :: FreshM m => ModPath -> Ident -> Range -> Name -> m Name
newModParam m i rng n = liftSupply (mkModParam m i rng n)


{- | Do something in the context of a module.
If `Nothing` than we are working with a local declaration.
Otherwise we are at the top-level of the given module.

By wrapping types with this, we can pass the module path
to methdods that need the extra information. -}
data InModule a = InModule (Maybe ModPath) a
                  deriving (Functor,Traversable,Foldable,Show)




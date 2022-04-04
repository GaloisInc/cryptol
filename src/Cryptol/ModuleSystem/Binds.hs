{-# Language BlockArguments #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Cryptol.ModuleSystem.Binds where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Control.Monad(foldM)
import MonadLib (runId,Id,StateT,runStateT,lift,sets_,forM_)
import qualified MonadLib as M

import Cryptol.Utils.Panic (panic)
import Cryptol.Parser.Position
import Cryptol.Parser.Name(isGeneratedName)
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface



--------------------------------------------------------------------------------
-- XXX: TopDef and friends subsumes OwnedEntitities and they shoudl be removed


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

  , modState     :: a
    {- ^ Used in the import loop to track the current state of processing.
         The reason this is here, rather than just having a pair in the
         other algorithm is because this type is recursive (for nested modules)
         and it is conveninet to keep track for all modules at once -}
  }

instance Functor Mod where
  fmap f m = m { modState = f (modState m)
               , modMods  = fmap f <$> modMods m
               }

data TopDefError = MultipleDefinitions (Maybe ModPath) Ident [Range]
                 | UnexpectedNest Range PName

type ModBuilder = SupplyT (M.ExceptionT TopDefError Id)

modBuilder :: Supply -> ModBuilder a -> Either TopDefError (a, Supply)
modBuilder s m = M.runId (M.runExceptionT (runSupplyT s m))

defErr :: TopDefError -> ModBuilder a
defErr a = M.lift (M.raise a)

defNames :: BuildNamingEnv -> ModBuilder NamingEnv
defNames b = liftSupply \s -> M.runId (runSupplyT s (runBuild b))


topModuleDefs :: Module PName -> ModBuilder TopDef
topModuleDefs m =
  case mDef m of
    NormalModule ds -> TopMod mname <$> declsToMod (Just (TopModule mname)) ds
    FunctorInstanceOld f ds ->
      TopInstOld mname (thing f) <$> declsToMod Nothing ds
    FunctorInstance f as ->
      pure (TopInst mname (thing f) as)

  where
  mname = thing (mName m)

topDeclsDefs :: [TopDecl PName] -> ModBuilder (Mod ())
topDeclsDefs = declsToMod Nothing


declsToMod :: Maybe ModPath -> [TopDecl PName] -> ModBuilder (Mod ())
declsToMod mbPath ds =
  do defs <- defNames (foldMap (namingEnv . InModule mbPath) ds)
     case findAmbig defs of
       bad@(f : _) : _ ->
         defErr (MultipleDefinitions mbPath (nameIdent f) (map nameLoc bad))
       _ -> pure ()

     let mo = Mod { modImports      = [ thing i | DImport i <- ds ]
                  , modParams       = any isParamDecl ds
                  , modInstances    = mempty
                  , modMods         = mempty
                  , modSigs         = mempty
                  , modDefines      = defs
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
                         Just (One x)    -> x
                         _ -> panic "declsToMod" ["Missed ambig/undefined"]
           case mbPath of
             Nothing -> defErr (UnexpectedNest (srcRange (mName nmod)) pname)
             Just path ->
                case mDef nmod of
                   NormalModule xs ->
                     do m <- declsToMod (Just (Nested path (nameIdent name))) xs
                        pure mo { modMods = Map.insert name m (modMods mo) }
                   FunctorInstanceOld {} ->
                     defErr (UnexpectedNest (srcRange (mName nmod)) pname)
                   FunctorInstance f args ->
                      pure mo { modInstances = Map.insert name (thing f, args)
                                                    (modInstances mo) }

      -- DModSig (TopLevel (Signature name))         -- ^ A module signature
      DModSig tl ->
        do let sig   = tlValue tl
               pname = thing (sigName sig)
               name  = case lookupNS NSSignature pname defs of
                         Just (One x) -> x
                         _ -> panic "declsToMod" ["sig: Missed ambig/undefined"]
           case mbPath of
             Nothing -> defErr (UnexpectedNest (srcRange (sigName sig)) pname)
             Just path ->
                do newEnv <-
                     defNames (signatureDefs (Nested path (nameIdent name)) sig)
                   pure mo { modSigs = Map.insert name newEnv (modSigs mo) }

      _ -> pure mo







--------------------------------------------------------------------------------
{- Collect definitions of entities that may contains other entities.
For example, submodules and signatures, when treated as declarations
only introduce a single name (e.g., the name of the submodule or signature)
but when used can introduce additional names (e.g., in an import or
a submodule declaration).  The code in the following section computes the
names that are "owned" by all the entities, when "used".
-}


data OwnedEntities = OwnedEntities
  { ownSubmodules :: Map Name NamingEnv
  , ownFunctors   :: Set Name
  , ownInstances  :: Map Name
                         (Located (ImpName PName), ModuleInstanceArgs PName)
  , ownSignatures :: Map Name NamingEnv
  }

instance Semigroup OwnedEntities where
  x <> y = OwnedEntities { ownSubmodules = ownSubmodules x <> ownSubmodules y
                         , ownFunctors   = ownFunctors x <> ownFunctors y
                         , ownInstances  = ownInstances x <> ownInstances y
                         , ownSignatures = ownSignatures x <> ownSignatures y
                         }

instance Monoid OwnedEntities where
  mempty = OwnedEntities { ownSubmodules = mempty
                         , ownFunctors   = mempty
                         , ownInstances  = mempty
                         , ownSignatures = mempty
                         }

type CollectM   = StateT OwnedEntities (SupplyT Id)

-- | Collect things nested in a module
collectNestedInModule ::
  NamingEnv -> Module PName -> Supply -> (OwnedEntities, Supply)
collectNestedInModule env m =
  case mDef m of
    NormalModule ds         -> collectNestedInDecls env (thing (mName m)) ds
    FunctorInstanceOld _ ds -> collectNestedInDecls env (thing (mName m)) ds
    FunctorInstance {}      -> \s -> (mempty, s)
      -- XXX: since this a top-level module, we *could* do the instantiation
      -- right here as the functor and its arguments which must be other
      -- top-level modules, and so are known.


-- | Collect things nested in a list of declarations
collectNestedInDecls ::
  NamingEnv -> ModName -> [TopDecl PName] -> Supply -> (OwnedEntities, Supply)
collectNestedInDecls env m ds sup = (mp,newS)
  where
  s0            = mempty
  mpath         = TopModule m
  ((_,mp),newS) = runId $ runSupplyT sup $ runStateT s0 $
                  collectNestedDeclsM mpath env ds

collectNestedDeclsM :: ModPath -> NamingEnv -> [TopDecl PName] -> CollectM ()
collectNestedDeclsM mpath env ds =

  do forM_ [ tlValue s | DModSig s <- ds ] \s ->
        do let pname = thing (sigName s)
               name  = case lookupNS NSSignature pname env of
                        Just ns -> anyOne ns
                        Nothing -> panic "collectNestedDeclsM"
                                    [ "Missing definition for " ++ show pname ]
                        -- See comment below.

           newEnv <- lift $ runBuild $
                    signatureDefs (Nested mpath (nameIdent name)) s
           sets_ \o -> o { ownSignatures = Map.insert name newEnv
                                                        (ownSignatures o)}

     forM_ [ tlValue nm | DModule nm <- ds ] \(NestedModule nested) ->
       do let pname = thing (mName nested)
              name  = case lookupNS NSModule pname env of
                        Just ns -> anyOne ns
                        Nothing -> panic "collectNestedDeclsM"
                                    [ "Missing definition for " ++ show pname ]
              -- if a name is ambiguous we may get
              -- multiple answers, but we just pick one.
              -- This should be OK, as the error should be
              -- caught during actual renaming.

          newEnv <- lift $ runBuild $
                      moduleDefs (Nested mpath (nameIdent name)) nested
          sets_ \o -> o { ownSubmodules =
                            Map.insert name newEnv (ownSubmodules o)
                        , ownFunctors =
                            if mIsFunctor nested
                              then Set.insert name (ownFunctors o)
                              else ownFunctors o
                        }
          let newMPath = Nested mpath (nameIdent name)
          case mDef nested of
            NormalModule des -> collectNestedDeclsM newMPath newEnv des
            FunctorInstanceOld _ des ->
              collectNestedDeclsM newMPath newEnv des
            FunctorInstance f as ->
              sets_ \o -> o { ownInstances = Map.insert name
                                                        (f,as)
                                                        (ownInstances o) }


-- | These are the names "owned" by the module.
-- These names are used when resolving the module itself.
moduleDefs :: ModPath -> ModuleG mname PName -> BuildNamingEnv
moduleDefs m mo =
  case mDef mo of
    NormalModule ds -> doDecls ds
    FunctorInstanceOld _ ds -> doDecls ds
    FunctorInstance {} -> mempty
  where
  doDecls = foldMap (namingEnv . InModule (Just m))

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

newtype BuildNamingEnv = BuildNamingEnv { runBuild :: SupplyT Id NamingEnv }

buildNamingEnv :: BuildNamingEnv -> Supply -> (NamingEnv,Supply)
buildNamingEnv b supply = runId $ runSupplyT supply $ runBuild b

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

-- | The naming environment for a single module.  This is the mapping from
-- unqualified names to fully qualified names with uniques.
instance BindsNames (Module PName) where
  namingEnv m = moduleDefs (TopModule (thing (mName m))) m


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




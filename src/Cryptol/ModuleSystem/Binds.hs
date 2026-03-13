{-# Language BlockArguments #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
module Cryptol.ModuleSystem.Binds
  ( BindsNames
  , ModKind(..)
  , modBuilder
  , newModParam
  , newFunctorInst
  , InModule(..)
  , defsOf
  , defsOfSig
  , defsOfPats
  ) where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Control.Monad(forM)
import qualified MonadLib as M

import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap(displayElements)
import Cryptol.Parser.Position
import Cryptol.Parser.Name(isSystemName, pattern UnQual)
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv


type ModBuilder = SupplyT (M.StateT [RenamerError] M.Id)

modBuilder :: ModBuilder a -> Supply -> ((a, [RenamerError]),Supply)
modBuilder m s = ((a,errs),s1)
  where ((a,s1),errs) = M.runId (M.runStateT [] (runSupplyT s m))

-- | These are the names "owned" by the signature.  These names are
-- used when resolving the signature.  They are also used to figure out what
-- names to instantiate when the signature is used.
signatureDefs :: ModPath -> Signature PName -> BuildNamingEnv
signatureDefs m sig =
     mconcat [ namingEnv (InModule loc p) | p <- sigTypeParams sig ]
  <> mconcat [ namingEnv (InModule loc p) | p <- sigFunParams sig ]
  <> mconcat [ namingEnv (InModule loc p) | p <- sigDecls sig ]
  where
  loc = Just m

defsOfSig :: ModPath -> Signature PName -> Supply -> (NamingEnv,Supply)
defsOfSig m sig = buildNamingEnv (signatureDefs m sig)
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
      DParamDecl {}    -> mempty -- shouldn't happen
      Include {}       -> mempty
      DImport {}       -> mempty -- Handled in renamer
      DModule m        -> namingEnv (InModule ns (tlValue m))
      DModParam {}     -> mempty -- Handled in renamer
      DInterfaceConstraint {} -> mempty
      

instance BindsNames (InModule (NestedModule PName)) where
  namingEnv (InModule mb (NestedModule mdef)) =
    case mb of
      Just m -> BuildNamingEnv $
        do
          let pnmame = mName mdef
          nm   <- newTop NSModule m (thing pnmame) Nothing (srcRange pnmame)
          pure (singletonNS NSModule (thing pnmame) nm)
      Nothing -> panic "BindsNames (InModule (NestedModule PName))" ["Nothing"]

instance BindsNames (InModule (PrimType PName)) where
  namingEnv (InModule mb PrimType { .. }) =
    case mb of
      Just m ->
        BuildNamingEnv $
          do let Located { .. } = primTName
             nm <- newTop NSType m thing primTFixity srcRange
             pure (singletonNS NSType thing nm)
      Nothing -> panic "BindsNames (InModule (PrimType PName))" ["Nothing"]

instance BindsNames (InModule (ParameterFun PName)) where
  namingEnv (InModule mb ParameterFun { .. }) =
    case mb of
      Just ns -> BuildNamingEnv $
        do
          let Located { .. } = pfName
          ntName <- newTop NSValue ns thing pfFixity srcRange
          return (singletonNS NSValue thing ntName)
      Nothing -> panic "BindsNames (InModule (ParameterFun PName))" ["Nothing"]

instance BindsNames (InModule (ParameterType PName)) where
  namingEnv (InModule mb ParameterType { .. }) =
    case mb of
      Just ns -> BuildNamingEnv $
        -- XXX: we don't seem to have a fixity environment at the type level
        do
          let Located { .. } = ptName
          ntName <- newTop NSType ns thing Nothing srcRange
          return (singletonNS NSType thing ntName)
      Nothing -> panic "BindsNames (InModule (ParameterType PName))" ["Nothing"]

instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule mb Newtype { .. }) =
    case mb of
      Just ns -> BuildNamingEnv $
        do let Located { .. } = nName
           ntName    <- newTop NSType  ns thing Nothing srcRange
           ntConName <- newTop NSConstructor ns thing Nothing srcRange
           return (singletonNS NSType thing ntName `mappend`
                   singletonNS NSConstructor thing ntConName)
      Nothing -> panic "BindsNames (InModule (Newtype PName))" ["Nothing"]

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


type PatsM = M.StateT (Set Ident) (SupplyT M.Id)

-- | We have a special case for this, because of the existential types
-- that we might encounter in the types of patterns.   In particular, if
-- we see `p : T` and `T` mentions a name `a` which is not otherwise defined,
-- we treat it as a new existential variable, and it is now considered defined
-- (i.e., other references to `a` should use the same name).
defsOfPats ::
  Set Ident {- ^ Unqalified type level names that are in scope -} ->
  [Pattern PName] {- ^ We want to know what names are introduced by these -} ->
  Supply -> (NamingEnv,Supply)
defsOfPats bound ps s =
  M.runId (runSupplyT s (fst <$> M.runStateT bound (defsOfPats' ps)))

defsOfPats' :: [Pattern PName] -> PatsM NamingEnv
defsOfPats' ps =
  case ps of
    []        -> pure mempty
    p : more  -> (<>) <$> defsOfPat p <*> defsOfPats' more

defsOfPat :: Pattern PName -> PatsM NamingEnv
defsOfPat pat =
  case pat of

    PVar x ->
      do
        y <- newLocal NSValue (thing x) (srcRange x)
        pure (singletonNS NSValue (thing x) y) 

    PCon _ xs     -> defsOfPats' xs
    PLocated p _r -> defsOfPat p
    PTyped p t    -> (<>) <$> defsOfTy t <*> defsOfPat p
    _             -> panic "namingEnv" ["Unexpected pattern"]

-- | Look for "naming" type variables in the type.
defsOfTy :: Type PName -> PatsM NamingEnv
defsOfTy ty =
  case ty of
    TFun a b -> defsOfTys [a,b]
    TSeq n t -> defsOfTys [n,t]
    TBit     -> pure mempty
    TNum {}  -> pure mempty
    TChar {} -> pure mempty

    TUser Located { thing = nm@(UnQual i), srcRange = rng  } [] ->
      do
        bound <- M.get
        if i `Set.member` bound
          then pure mempty
          else
            do
              y <- newLocal NSType nm rng
              M.sets (\b -> (singletonNS NSType nm y, Set.insert i b))

    TUser _ ts        -> defsOfTys ts
    TTyApp {}         -> panic "defsOfTy" ["TTyApp"]
    TRecord r         -> defsOfTys (map snd (displayElements r))
    TTuple ts         -> defsOfTys ts
    TWild             -> pure mempty
    TLocated t _      -> defsOfTy t
    TParens t _       -> defsOfTy t
    TInfix t1 _ _ t2  -> defsOfTys [t1,t2]
    
defsOfTys :: [Type PName] -> PatsM NamingEnv
defsOfTys tys =
  case tys of
    t : more  -> (<>) <$> defsOfTy t <*> defsOfTys more
    []        -> pure mempty



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




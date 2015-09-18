-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Cryptol.ModuleSystem.NamingEnv where

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name
import Cryptol.Parser.AST
import Cryptol.Parser.Names (namesP)
import Cryptol.Parser.Position
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)

import Data.Maybe (catMaybes,fromMaybe)
import qualified Data.Map as Map

import GHC.Generics (Generic)
import Control.DeepSeq

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Data.Monoid (Monoid(..))
import Data.Foldable (Foldable,foldMap)
import Data.Traversable (Traversable,traverse)
#endif


-- Naming Environment ----------------------------------------------------------

-- XXX The fixity environment should be removed, and Name should include fixity
-- information.
data NamingEnv = NamingEnv { neExprs :: Map.Map PName [Name]
                             -- ^ Expr renaming environment
                           , neTypes :: Map.Map PName [Name]
                             -- ^ Type renaming environment
                           , neFixity:: Map.Map Name [Fixity]
                             -- ^ Expression-level fixity environment
                           } deriving (Show, Generic)

instance NFData NamingEnv

instance Monoid NamingEnv where
  mempty        =
    NamingEnv { neExprs  = Map.empty
              , neTypes  = Map.empty
              , neFixity = Map.empty }

  mappend l r   =
    NamingEnv { neExprs  = Map.unionWith (++) (neExprs  l) (neExprs  r)
              , neTypes  = Map.unionWith (++) (neTypes  l) (neTypes  r)
              , neFixity = Map.unionWith (++) (neFixity l) (neFixity r) }

  mconcat envs  =
    NamingEnv { neExprs  = Map.unionsWith (++) (map neExprs  envs)
              , neTypes  = Map.unionsWith (++) (map neTypes  envs)
              , neFixity = Map.unionsWith (++) (map neFixity envs) }


-- | Singleton type renaming environment.
singletonT :: PName -> Name -> NamingEnv
singletonT qn tn = mempty { neTypes = Map.singleton qn [tn] }

-- | Singleton expression renaming environment.
singletonE :: PName -> Name -> NamingEnv
singletonE qn en = mempty { neExprs = Map.singleton qn [en] }

-- | Like mappend, but when merging, prefer values on the lhs.
shadowing :: NamingEnv -> NamingEnv -> NamingEnv
shadowing l r = NamingEnv
  { neExprs  = Map.union (neExprs  l) (neExprs  r)
  , neTypes  = Map.union (neTypes  l) (neTypes  r)
  , neFixity = Map.union (neFixity l) (neFixity r) }

travNamingEnv :: Applicative f => (Name -> f Name) -> NamingEnv -> f NamingEnv
travNamingEnv f ne = NamingEnv <$> neExprs' <*> neTypes' <*> pure (neFixity ne)
  where
    neExprs' = traverse (traverse f) (neExprs ne)
    neTypes' = traverse (traverse f) (neTypes ne)


data InModule a = InModule !ModName a
                  deriving (Functor,Traversable,Foldable,Show)


-- | Things that define exported names.
class BindsNames a where
  namingEnv :: a -> SupplyM NamingEnv

instance BindsNames NamingEnv where
  namingEnv = return

instance BindsNames a => BindsNames (Maybe a) where
  namingEnv = foldMap namingEnv

instance BindsNames a => BindsNames [a] where
  namingEnv = foldMap namingEnv

-- | Generate a type renaming environment from the parameters that are bound by
-- this schema.
instance BindsNames (Schema PName) where
  namingEnv (Forall ps _ _ _) = foldMap namingEnv ps

-- -- | Produce a naming environment from an interface file, that contains a
-- -- mapping only from unqualified names to qualified ones.
-- instance BindsNames Iface where
--   namingEnv = namingEnv . ifPublic

-- -- | Translate a set of declarations from an interface into a naming
-- -- environment.
-- instance BindsNames IfaceDecls where
--   namingEnv binds = mconcat [ types, newtypes, vars ]
--     where

--     types = mempty
--       { neTypes = Map.map (map (TFromMod . ifTySynName)) (ifTySyns binds)
--       }

--     newtypes = mempty
--       { neTypes = Map.map (map (TFromMod . T.ntName)) (ifNewtypes binds)
--       , neExprs = Map.map (map (EFromMod . T.ntName)) (ifNewtypes binds)
--       }

--     vars = mempty
--       { neExprs  = Map.map (map (EFromMod . ifDeclName)) (ifDecls binds)
--       , neFixity = Map.fromList [ (n,fs) | ds <- Map.elems (ifDecls binds)
--                                          , all ifDeclInfix ds
--                                          , let fs = catMaybes (map ifDeclFixity ds)
--                                                n  = ifDeclName (head ds) ]
--       }


-- -- | Translate names bound by the patterns of a match into a renaming
-- -- environment.
-- instance BindsNames Match where
--   namingEnv m = case m of
--     Match p _  -> namingEnv p
--     MatchLet b -> namingEnv b

-- | Introduce the name 
instance BindsNames (InModule (Bind PName)) where
  namingEnv (InModule ns b) =
    do let Located { .. } = bName b
       n <- liftSupply (mkDeclared ns (getIdent thing) srcRange)

       let fixity = case bFixity b of
             Just f  -> mempty { neFixity = Map.singleton n [f] }
             Nothing -> mempty

       return (singletonE thing n `mappend` fixity)

-- | Generate the naming environment for a type parameter.
instance BindsNames (TParam PName) where
  namingEnv TParam { .. } =
    do let range = fromMaybe emptyRange tpRange
       n <- liftSupply (mkParameter (getIdent tpName) range)
       return (singletonT tpName n)

-- -- | Generate an expression renaming environment from a pattern.  This ignores
-- -- type parameters that can be bound by the pattern.
-- instance BindsNames (AtLoc (Pattern PName)) where
--   namingEnv (AtLoc loc p0) = go loc p0
--     where
--     go loc (PVar Located { .. }) =
--       do n <- liftSupply (mkParameter (getIdent thing) loc)
--          return (singletonE thing n)

--     go _   PWild            = return mempty
--     go loc (PTuple ps)      = foldMap (go loc) ps
--     go loc (PRecord fs)     = foldMap (foldMap (go loc)) fs
--     go loc (PList ps)       = foldMap (go loc) ps
--     go loc (PTyped p ty)    = go loc p `mappend` namingEnv (AtLoc loc ty)
--     go loc (PSplit a b)     = go loc a `mappend` go loc b
--     go _   (PLocated p loc) = go loc p

-- -- | Introduce the binding environment for all variables present in a type.
-- instance BindsNames (WithEnv (AtLoc (Type PName))) where
--   namingEnv (AtLoc loc ty0) = go loc ty0
--     where
--     go loc (TFun a b) = go loc a `mappend` go loc b
--     go loc (TSeq a b) = go loc a `mappend` go loc b
--     go _   TBit = return mempty
--     go _   TNum{} = return mempty
--     go _   TChar{} = return mempty
--     go _   TInf = return mempty
--     go loc (TUser n [Type n]        -- ^ A type variable or synonym
--     go loc (TApp TFun [Type n]      -- ^ @2 + x@
--     go loc (TRecord [Named (Type n)]-- ^ @{ x : [8], y : [32] }@
--     go loc (TTuple [Type n]         -- ^ @([8], [32])@
--     go loc (TWild                   -- ^ @_@, just some type.
--     go loc (TLocated (Type n) Range -- ^ Location information
--     go loc (TParens (Type n)        -- ^ @ (ty) @
--     go loc (TInfix (Type n) (Located n) Fixity (Type n) -- ^ @ ty + ty @


-- | The naming environment for a single module.  This is the mapping from
-- unqualified names to fully qualified names with uniques.
instance BindsNames (Module PName) where
  namingEnv Module { .. } = foldMap (namingEnv . InModule ns) mDecls
    where
    ns = thing mName

instance BindsNames (InModule (TopDecl PName)) where
  namingEnv (InModule ns td) =
    case td of
      Decl td      -> namingEnv (InModule ns (tlValue td))
      TDNewtype td -> namingEnv (InModule ns (tlValue td))
      Include _    -> return mempty

instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ns Newtype { .. }) =
    do let Located { .. } = nName
       tyName <- liftSupply (mkDeclared ns (getIdent thing) srcRange)
       eName  <- liftSupply (mkDeclared ns (getIdent thing) srcRange)
       return (singletonT thing tyName `mappend` singletonE thing eName)

-- | The naming environment for a single declaration.
instance BindsNames (InModule (Decl PName)) where
  namingEnv (InModule ns d) = case d of
    DBind b ->
      do n <- mkName (bName b)
         return (singletonE (thing (bName b)) n `mappend` fixity n b)

    DSignature ns _sig    -> foldMap qualBind ns
    DPragma ns _p         -> foldMap qualBind ns
    DType (TySyn lqn _ _) -> qualType lqn
    DLocated d' _         -> namingEnv (InModule ns d')
    DPatBind _pat _e      -> panic "ModuleSystem" ["Unexpected pattern binding"]
    DFixity{}             -> panic "ModuleSystem" ["Unexpected fixity declaration"]

    where

    mkName ln =
      liftSupply (mkDeclared ns (getIdent (thing ln)) (srcRange ln))

    qualBind ln =
      do n <- mkName ln
         return (singletonE (thing ln) n)

    qualType ln =
      do n <- mkName ln
         return (singletonT (thing ln) n)

    fixity n b =
      case bFixity b of
        Just f  -> mempty { neFixity = Map.singleton n [f] }
        Nothing -> mempty

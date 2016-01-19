-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
-- for the instances of RunM and BaseM
{-# LANGUAGE UndecidableInstances #-}

module Cryptol.ModuleSystem.Name (
    -- * Names
    Name(), NameInfo(..)
  , nameUnique
  , nameIdent
  , nameInfo
  , nameLoc
  , asPrim
  , cmpNameLexical
  , cmpNameDisplay
  , ppLocName

    -- ** Creation
  , mkDeclared
  , mkParameter

    -- ** Unique Supply
  , FreshM(..), nextUniqueM
  , SupplyT(), runSupplyT
  , SupplyM(), runSupplyM
  , Supply(), emptySupply, nextUnique

    -- ** PrimMap
  , PrimMap(..)
  , lookupPrimDecl
  , lookupPrimType
  ) where

import           Cryptol.Parser.Position (Range,Located(..))
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP

import           Control.DeepSeq.Generics
import           Control.Monad.Fix (MonadFix(mfix))
import qualified Data.Map as Map
import qualified Data.Monoid as M
import           Data.Ord (comparing)
import           GHC.Generics (Generic)
import           MonadLib
import           Prelude ()
import           Prelude.Compat


-- Names -----------------------------------------------------------------------
-- | Information about the binding site of the name.
data NameInfo = Declared !ModName
                -- ^ This name refers to a declaration from this module
              | Parameter
                -- ^ This name is a parameter (function or type)
                deriving (Eq,Show,Generic)

data Name = Name { nUnique :: {-# UNPACK #-} !Int
                   -- ^ INVARIANT: this field uniquely identifies a name for one
                   -- session with the Cryptol library. Names are unique to
                   -- their binding site.

                 , nInfo :: !NameInfo
                   -- ^ Information about the origin of this name.

                 , nIdent :: !Ident
                   -- ^ The name of the identifier

                 , nLoc :: !Range
                   -- ^ Where this name was defined
                 } deriving (Show,Generic)

instance Eq Name where
  a == b = compare a b == EQ
  a /= b = compare a b /= EQ

instance Ord Name where
  compare a b = compare (nUnique a) (nUnique b)

instance NFData NameInfo where rnf = genericRnf
instance NFData Name where rnf = genericRnf

-- | Compare two names lexically.
cmpNameLexical :: Name -> Name -> Ordering
cmpNameLexical l r =
  case (nameInfo l, nameInfo r) of

    (Declared nsl,Declared nsr) ->
      case compare nsl nsr of
        EQ  -> comparing nameIdent l r
        cmp -> cmp

    (Parameter,Parameter) -> comparing nameIdent l r

    (Declared nsl,Parameter) -> compare nsl (identText (nameIdent r))
    (Parameter,Declared nsr) -> compare (identText (nameIdent l)) nsr


-- | Compare two names by the way they would be displayed.
cmpNameDisplay :: NameDisp -> Name -> Name -> Ordering
cmpNameDisplay disp l r =
  case (nameInfo l, nameInfo r) of

    (Declared nsl, Declared nsr) ->
      let pfxl = fmtModName nsl (getNameFormat nsl (nameIdent l) disp)
          pfxr = fmtModName nsr (getNameFormat nsr (nameIdent r) disp)
       in case compare pfxl pfxr of
            EQ  -> compare (nameIdent l) (nameIdent r)
            cmp -> cmp

    (Parameter,Parameter) ->
      compare (nameIdent l) (nameIdent r)

    (Declared nsl,Parameter) ->
      let pfxl = fmtModName nsl (getNameFormat nsl (nameIdent l) disp)
       in case compare pfxl (identText (nameIdent r)) of
            EQ  -> GT
            cmp -> cmp

    (Parameter,Declared nsr) ->
      let pfxr = fmtModName nsr (getNameFormat nsr (nameIdent r) disp)
       in case compare (identText (nameIdent l)) pfxr of
            EQ  -> LT
            cmp -> cmp


-- | Figure out how the name should be displayed, by referencing the display
-- function in the environment. NOTE: this function doesn't take into account
-- the need for parenthesis.
ppName :: Name -> Doc
ppName Name { .. } =
  case nInfo of

    Declared m -> withNameDisp $ \disp ->
      case getNameFormat m nIdent disp of
        Qualified m' -> pp m' <> text "::" <> pp nIdent
        UnQualified  ->                       pp nIdent
        NotInScope   -> pp m  <> text "::" <> pp nIdent

    Parameter -> pp nIdent

instance PP Name where
  ppPrec _ = ppPrefixName

instance PPName Name where
  ppInfixName n @ Name { .. }
    | isInfixIdent nIdent = ppName n
    | otherwise           = panic "Name" [ "Non-infix name used infix"
                                         , show nIdent ]

  ppPrefixName n @ Name { .. } = optParens (isInfixIdent nIdent) (ppName n)

-- | Pretty-print a name with its source location information.
ppLocName :: Name -> Doc
ppLocName n = pp Located { srcRange = nameLoc n, thing = n }

nameUnique :: Name -> Int
nameUnique  = nUnique

nameIdent :: Name -> Ident
nameIdent  = nIdent

nameInfo :: Name -> NameInfo
nameInfo  = nInfo

nameLoc :: Name -> Range
nameLoc  = nLoc

asPrim :: Name -> Maybe Ident
asPrim Name { .. }
  | nInfo == Declared preludeName = Just nIdent
  | otherwise                     = Nothing


-- Name Supply -----------------------------------------------------------------

class Monad m => FreshM m where
  liftSupply :: (Supply -> (a,Supply)) -> m a

instance FreshM m => FreshM (ExceptionT i m) where
  liftSupply f = lift (liftSupply f)

instance (M.Monoid i, FreshM m) => FreshM (WriterT i m) where
  liftSupply f = lift (liftSupply f)

instance FreshM m => FreshM (ReaderT i m) where
  liftSupply f = lift (liftSupply f)

instance FreshM m => FreshM (StateT i m) where
  liftSupply f = lift (liftSupply f)

instance FreshM SupplyM where
  liftSupply f = SupplyM (liftSupply f)

instance Monad m => FreshM (SupplyT m) where
  liftSupply f = SupplyT $
    do s <- get
       let (a,s') = f s
       set $! s'
       return a

-- | A monad for easing the use of the supply.
newtype SupplyT m a = SupplyT { unSupply :: StateT Supply m a }

runSupplyT :: Monad m => Supply -> SupplyT m a -> m (a,Supply)
runSupplyT s (SupplyT m) = runStateT s m

instance Monad m => Functor (SupplyT m) where
  fmap f (SupplyT m) = SupplyT (fmap f m)
  {-# INLINE fmap #-}

instance Monad m => Applicative (SupplyT m) where
  pure x = SupplyT (pure x)
  {-# INLINE pure #-}

  f <*> g = SupplyT (unSupply f <*> unSupply g)
  {-# INLINE (<*>) #-}

instance Monad m => Monad (SupplyT m) where
  return = pure
  {-# INLINE return #-}

  m >>= f = SupplyT (unSupply m >>= unSupply . f)
  {-# INLINE (>>=) #-}

instance MonadT SupplyT where
  lift m = SupplyT (lift m)

instance BaseM m n => BaseM (SupplyT m) n where
  inBase m = SupplyT (inBase m)
  {-# INLINE inBase #-}

instance RunM m (a,Supply) r => RunM (SupplyT m) a (Supply -> r) where
  runM (SupplyT m) s = runM m s
  {-# INLINE runM #-}

instance MonadFix m => MonadFix (SupplyT m) where
  mfix f = SupplyT (mfix (unSupply . f))


newtype SupplyM a = SupplyM (SupplyT Id a)
                    deriving (Functor,Applicative,Monad,MonadFix)

runSupplyM :: Supply -> SupplyM a -> (a,Supply)
runSupplyM s m = runM m s

instance RunM SupplyM a (Supply -> (a,Supply)) where
  runM (SupplyM m) s = runM m s
  {-# INLINE runM #-}

instance BaseM SupplyM SupplyM where
  inBase = id
  {-# INLINE inBase #-}

instance M.Monoid a => M.Monoid (SupplyM a) where
  mempty      = return mempty
  mappend a b = do x <- a
                   y <- b
                   return (mappend x y)

-- | Retrieve the next unique from the supply.
nextUniqueM :: FreshM m => m Int
nextUniqueM  = liftSupply nextUnique


data Supply = Supply !Int
              deriving (Show,Generic)

instance NFData Supply where rnf = genericRnf

-- | This should only be used once at library initialization, and threaded
-- through the rest of the session.  The supply is started at 0x1000 to leave us
-- plenty of room for names that the compiler needs to know about (wired-in
-- constants).
emptySupply :: Supply
emptySupply  = Supply 0

nextUnique :: Supply -> (Int,Supply)
nextUnique (Supply n) = s' `seq` (n,s')
  where
  s' = Supply (n + 1)


-- Name Construction -----------------------------------------------------------

-- | Make a new name for a declaration.
mkDeclared :: ModName -> Ident -> Range -> Supply -> (Name,Supply)
mkDeclared m nIdent nLoc s =
  let (nUnique,s') = nextUnique s
      nInfo        = Declared m
   in (Name { .. }, s')

-- | Make a new parameter name.
mkParameter :: Ident -> Range -> Supply -> (Name,Supply)
mkParameter nIdent nLoc s =
  let (nUnique,s') = nextUnique s
   in (Name { nInfo = Parameter, .. }, s')


-- Prim Maps -------------------------------------------------------------------

-- | A mapping from an identifier defined in some module to its real name.
data PrimMap = PrimMap { primDecls :: Map.Map Ident Name
                       , primTypes :: Map.Map Ident Name
                       } deriving (Show, Generic)

instance NFData PrimMap where rnf = genericRnf

lookupPrimDecl, lookupPrimType :: Ident -> PrimMap -> Name

-- | It's assumed that we're looking things up that we know already exist, so
-- this will panic if it doesn't find the name.
lookupPrimDecl name PrimMap { .. } = Map.findWithDefault err name primDecls
  where
  err = panic "Cryptol.ModuleSystem.Name.lookupPrimDecl"
        [ "Unknown declaration: " ++ show name
        , show primDecls ]

-- | It's assumed that we're looking things up that we know already exist, so
-- this will panic if it doesn't find the name.
lookupPrimType name PrimMap { .. } = Map.findWithDefault err name primTypes
  where
  err = panic "Cryptol.ModuleSystem.Name.lookupPrimType"
        [ "Unknown type: " ++ show name
        , show primTypes ]

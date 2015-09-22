{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

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

    -- ** Creation
  , mkDeclared
  , mkParameter

    -- ** Unique Supply
  , FreshM(..), nextUniqueM
  , SupplyT(), runSupplyT
  , SupplyM(), runSupplyM
  , Supply(), emptySupply, nextUnique

    -- * Name Maps
  , NameMap()
  , emptyNM
  , nullNM
  , insertNM
  , alterNM
  , lookupNM
  , findWithDefaultNM
  , unionWithNM
  , toListNM
  , mapMaybeWithKeyNM
  ) where

import           Cryptol.Parser.Position (Range)
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP

import qualified Control.Applicative as A
import           Control.DeepSeq
import qualified Data.IntMap.Lazy as I
import qualified Data.Monoid as M
import           GHC.Generics (Generic)
import           MonadLib


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

instance NFData NameInfo
instance NFData Name

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

instance BaseM m n => BaseM (SupplyT m) n where
  inBase m = SupplyT (inBase m)
  {-# INLINE inBase #-}

instance RunM m (a,Supply) r => RunM (SupplyT m) a (Supply -> r) where
  runM (SupplyT m) s = runM m s
  {-# INLINE runM #-}


newtype SupplyM a = SupplyM (SupplyT Id a)
                    deriving (Functor,A.Applicative,Monad)

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

-- | This should only be used once at library initialization, and threaded
-- through the rest of the session.  The supply is started at 0x1000 to leave us
-- plenty of room for names that the compiler needs to know about (wired-in
-- constants).
emptySupply :: Supply
emptySupply  = Supply 0x1000

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


-- Maps of Names ---------------------------------------------------------------

-- | Maps that take advantage of the unique key in names.
newtype NameMap a = NameMap { nmElems :: I.IntMap (Name,a)
                            } deriving (Functor,Foldable,Traversable,Show,Generic)

instance NFData a => NFData (NameMap a)

toListNM :: NameMap a -> [(Name,a)]
toListNM NameMap { .. } = I.elems nmElems

emptyNM :: NameMap a
emptyNM  = NameMap { nmElems = I.empty }

nullNM :: NameMap a -> Bool
nullNM NameMap { .. } = I.null nmElems

insertNM :: Name -> a -> NameMap a -> NameMap a
insertNM n a (NameMap ns) = NameMap (I.insert (nUnique n) (n,a) ns)

lookupNM :: Name -> NameMap a -> Maybe a
lookupNM Name { .. } (NameMap m) = snd `fmap` I.lookup nUnique m

alterNM :: Name -> (Maybe a -> Maybe a) -> NameMap a -> NameMap a
alterNM k f (NameMap m) = NameMap (I.alter f' (nUnique k) m)
  where
  f' (Just (n,a)) = do a' <- f (Just a)
                       return (n,a')
  f' Nothing      = do a  <- f Nothing
                       return (k,a)

findWithDefaultNM :: a -> Name -> NameMap a -> a
findWithDefaultNM a Name { .. } (NameMap m) =
  snd (I.findWithDefault (undefined,a) nUnique m)

unionWithNM :: (a -> a -> a) -> NameMap a -> NameMap a -> NameMap a
unionWithNM combine (NameMap a) (NameMap b) = NameMap (I.unionWith combine' a b)
  where
  -- As the uniques were the same, the name values will also be the same.
  combine' (n,x) (_,y) = (n,combine x y)

mapMaybeWithKeyNM :: (Name -> a -> Maybe b) -> NameMap a -> NameMap b
mapMaybeWithKeyNM f (NameMap m) = NameMap (I.mapMaybeWithKey f' m)
  where
  f' _ (n,a) = do b <- f n a
                  return (n,b)

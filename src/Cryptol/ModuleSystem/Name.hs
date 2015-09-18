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
  , SupplyM(), runSupplyM, nextUniqueM, liftSupply
  , Supply(), emptySupply, nextUnique

    -- * Name Maps
  , NameMap()
  , emptyNM
  , insertNM
  , lookupNM
  , findWithDefaultNM
  ) where

import           Cryptol.Parser.Position (Range)
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP

import qualified Control.Applicative as A
import           Control.DeepSeq
import qualified Data.Text as T
import qualified Data.IntMap.Lazy as I
import qualified Data.Monoid as M
import           GHC.Generics (Generic)
import           MonadLib


-- Names -----------------------------------------------------------------------

-- | Information about the origin of the name.
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

ppNamespace :: NameInfo -> Doc
ppNamespace (Declared modName) = pp modName <> text "::"
ppNamespace Parameter          = empty

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

-- | A monad for easing the use of the supply.
newtype SupplyM a = SupplyM (StateT Supply Lift a)
                    deriving (Functor,A.Applicative,Monad)

instance M.Monoid a => M.Monoid (SupplyM a) where
  mempty      = return mempty
  mappend a b = do x <- a
                   y <- b
                   return (mappend x y)

instance BaseM SupplyM SupplyM where
  inBase = id
  {-# INLINE inBase #-}

instance RunM SupplyM a (Supply -> (a,Supply)) where
  runM m s = runSupplyM s m
  {-# INLINE runM #-}

runSupplyM :: Supply -> SupplyM a -> (a,Supply)
runSupplyM s0 (SupplyM m) = runM m s0

-- | Retrieve the next unique from the supply.
nextUniqueM :: SupplyM Int
nextUniqueM  = SupplyM $
  do Supply n <- get
     set $! Supply (n+1)
     return n

-- | Lift an operation that uses a 'Supply' into the 'SupplyM' monad.
liftSupply :: (Supply -> (a,Supply)) -> SupplyM a
liftSupply f = SupplyM $
  do s <- get
     let (a,s') = f s
     set $! s'
     return a


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

newtype NameMap a = NameMap { nmElems :: I.IntMap (Name,a)
                            } deriving (Functor,Foldable,Traversable,Show)

emptyNM :: NameMap a
emptyNM  = NameMap { nmElems = I.empty }

insertNM :: Name -> a -> NameMap a -> NameMap a
insertNM n a (NameMap ns) = NameMap (I.insert (nUnique n) (n,a) ns)

lookupNM :: Name -> NameMap a -> Maybe a
lookupNM Name { .. } (NameMap m) = snd `fmap` I.lookup nUnique m

findWithDefaultNM :: a -> Name -> NameMap a -> a
findWithDefaultNM a Name { .. } (NameMap m) =
  snd (I.findWithDefault (undefined,a) nUnique m)

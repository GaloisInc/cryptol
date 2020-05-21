-- |
-- Module      :  Cryptol.ModuleSystem.Name
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Trustworthy #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
-- for the instances of RunM and BaseM
{-# LANGUAGE UndecidableInstances #-}

module Cryptol.ModuleSystem.Name (
    -- * Names
    Name(), NameInfo(..)
  , NameSource(..)
  , nameUnique
  , nameIdent
  , nameInfo
  , nameLoc
  , nameFixity
  , asPrim
  , cmpNameLexical
  , cmpNameDisplay
  , ppLocName

    -- ** Creation
  , mkDeclared
  , mkParameter
  , toParamInstName
  , asParamName
  , paramModRecParam

    -- ** Unique Supply
  , FreshM(..), nextUniqueM
  , SupplyT(), runSupplyT
  , Supply(), emptySupply, nextUnique

    -- ** PrimMap
  , PrimMap(..)
  , lookupPrimDecl
  , lookupPrimType
  ) where

import           Cryptol.Parser.Position (Range,Located(..),emptyRange)
import           Cryptol.Utils.Fixity
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP


import           Control.DeepSeq
import           Control.Monad.Fix (MonadFix(mfix))
import qualified Data.Map as Map
import qualified Data.Monoid as M
import           Data.Ord (comparing)
import qualified Data.Text as Text
import           Data.Char(isAlpha,toUpper)
import           GHC.Generics (Generic)
import           MonadLib
import           Prelude ()
import           Prelude.Compat


-- Names -----------------------------------------------------------------------
-- | Information about the binding site of the name.
data NameInfo = Declared !ModName !NameSource
                -- ^ This name refers to a declaration from this module
              | Parameter
                -- ^ This name is a parameter (function or type)
                deriving (Eq, Show, Generic, NFData)

data Name = Name { nUnique :: {-# UNPACK #-} !Int
                   -- ^ INVARIANT: this field uniquely identifies a name for one
                   -- session with the Cryptol library. Names are unique to
                   -- their binding site.

                 , nInfo :: !NameInfo
                   -- ^ Information about the origin of this name.

                 , nIdent :: !Ident
                   -- ^ The name of the identifier

                 , nFixity :: !(Maybe Fixity)
                   -- ^ The associativity and precedence level of
                   --   infix operators.  'Nothing' indicates an
                   --   ordinary prefix operator.

                 , nLoc :: !Range
                   -- ^ Where this name was defined
                 } deriving (Generic, NFData, Show)


data NameSource = SystemName | UserName
                    deriving (Generic, NFData, Show, Eq)

instance Eq Name where
  a == b = compare a b == EQ
  a /= b = compare a b /= EQ

instance Ord Name where
  compare a b = compare (nUnique a) (nUnique b)

-- | Compare two names lexically.
cmpNameLexical :: Name -> Name -> Ordering
cmpNameLexical l r =
  case (nameInfo l, nameInfo r) of

    (Declared nsl _,Declared nsr _) ->
      case compare nsl nsr of
        EQ  -> comparing nameIdent l r
        cmp -> cmp

    (Parameter,Parameter) -> comparing nameIdent l r

    (Declared nsl _,Parameter) -> compare (modNameToText nsl)
                                          (identText (nameIdent r))
    (Parameter,Declared nsr _) -> compare (identText (nameIdent l))
                                          (modNameToText nsr)


-- | Compare two names by the way they would be displayed.
cmpNameDisplay :: NameDisp -> Name -> Name -> Ordering
cmpNameDisplay disp l r =
  case (nameInfo l, nameInfo r) of

    (Declared nsl _, Declared nsr _) -> -- XXX: uses system name info?
      let pfxl = fmtModName nsl (getNameFormat nsl (nameIdent l) disp)
          pfxr = fmtModName nsr (getNameFormat nsr (nameIdent r) disp)
       in case cmpText pfxl pfxr of
            EQ  -> cmpName l r
            cmp -> cmp

    (Parameter,Parameter) -> cmpName l r

    (Declared nsl _,Parameter) ->
      let pfxl = fmtModName nsl (getNameFormat nsl (nameIdent l) disp)
       in case cmpText pfxl (identText (nameIdent r)) of
            EQ  -> GT
            cmp -> cmp

    (Parameter,Declared nsr _) ->
      let pfxr = fmtModName nsr (getNameFormat nsr (nameIdent r) disp)
       in case cmpText (identText (nameIdent l)) pfxr of
            EQ  -> LT
            cmp -> cmp

  where
  cmpName xs ys  = cmpIdent (nameIdent xs) (nameIdent ys)
  cmpIdent xs ys = cmpText (identText xs) (identText ys)

  -- Note that this assumes that `xs` is `l` and `ys` is `r`
  cmpText xs ys =
    case (Text.null xs, Text.null ys) of
      (True,True)   -> EQ
      (True,False)  -> LT
      (False,True)  -> GT
      (False,False) -> compare (cmp (fx l) xs) (cmp (fx r) ys)
        where
        fx a = fLevel <$> nameFixity a
        cmp a cs = (ordC (Text.index cs 0), a, cs)
        ordC a | isAlpha a  = fromEnum (toUpper a)
               | a == '_'   = 1
               | otherwise  = 0

-- | Figure out how the name should be displayed, by referencing the display
-- function in the environment. NOTE: this function doesn't take into account
-- the need for parenthesis.
ppName :: Name -> Doc
ppName Name { .. } =
  case nInfo of

    Declared m _ -> withNameDisp $ \disp ->
      case getNameFormat m nIdent disp of
        Qualified m' -> pp m' <.> text "::" <.> pp nIdent
        UnQualified  ->                         pp nIdent
        NotInScope   -> pp m  <.> text "::" <.> pp nIdent

    Parameter -> pp nIdent

instance PP Name where
  ppPrec _ = ppPrefixName

instance PPName Name where
  ppNameFixity n = nameFixity n

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

nameFixity :: Name -> Maybe Fixity
nameFixity = nFixity


asPrim :: Name -> Maybe PrimIdent
asPrim Name { .. } =
  case nInfo of
    Declared p _ -> Just $ PrimIdent p $ identText nIdent
    _            -> Nothing

toParamInstName :: Name -> Name
toParamInstName n =
  case nInfo n of
    Declared m s -> n { nInfo = Declared (paramInstModName m) s }
    Parameter   -> n

asParamName :: Name -> Name
asParamName n = n { nInfo = Parameter }


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

-- | Retrieve the next unique from the supply.
nextUniqueM :: FreshM m => m Int
nextUniqueM  = liftSupply nextUnique


data Supply = Supply !Int
              deriving (Show, Generic, NFData)

-- | This should only be used once at library initialization, and threaded
-- through the rest of the session.  The supply is started at 0x1000 to leave us
-- plenty of room for names that the compiler needs to know about (wired-in
-- constants).
emptySupply :: Supply
emptySupply  = Supply 0x1000
-- For one such name, see paramModRecParam
-- XXX: perhaps we should simply not have such things, but that's the way
-- for now.

nextUnique :: Supply -> (Int,Supply)
nextUnique (Supply n) = s' `seq` (n,s')
  where
  s' = Supply (n + 1)


-- Name Construction -----------------------------------------------------------

-- | Make a new name for a declaration.
mkDeclared :: ModName -> NameSource -> Ident -> Maybe Fixity -> Range -> Supply -> (Name,Supply)
mkDeclared m sys nIdent nFixity nLoc s =
  let (nUnique,s') = nextUnique s
      nInfo        = Declared m sys
   in (Name { .. }, s')

-- | Make a new parameter name.
mkParameter :: Ident -> Range -> Supply -> (Name,Supply)
mkParameter nIdent nLoc s =
  let (nUnique,s') = nextUnique s
      nFixity      = Nothing
   in (Name { nInfo = Parameter, .. }, s')

paramModRecParam :: Name
paramModRecParam = Name { nInfo = Parameter
                        , nFixity = Nothing
                        , nIdent  = packIdent "$modParams"
                        , nLoc    = emptyRange
                        , nUnique = 0x01
                        }

-- Prim Maps -------------------------------------------------------------------

-- | A mapping from an identifier defined in some module to its real name.
data PrimMap = PrimMap { primDecls :: Map.Map PrimIdent Name
                       , primTypes :: Map.Map PrimIdent Name
                       } deriving (Show, Generic, NFData)

instance Semigroup PrimMap where
  x <> y = PrimMap { primDecls = Map.union (primDecls x) (primDecls y)
                   , primTypes = Map.union (primTypes x) (primTypes y)
                   }

lookupPrimDecl, lookupPrimType :: PrimIdent -> PrimMap -> Name

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

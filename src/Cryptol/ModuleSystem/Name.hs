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
{-# LANGUAGE OverloadedStrings #-}
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
  , nameNamespace
  , asPrim
  , asOrigName
  , ppLocName
  , Namespace(..)
  , ModPath(..)
  , cmpNameDisplay

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

import           Control.DeepSeq
import qualified Data.Map as Map
import qualified Data.Monoid as M
import           GHC.Generics (Generic)
import           MonadLib
import           Prelude ()
import           Prelude.Compat
import qualified Data.Text as Text
import           Data.Char(isAlpha,toUpper)



import           Cryptol.Parser.Position (Range,Located(..),emptyRange)
import           Cryptol.Utils.Fixity
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP



-- Names -----------------------------------------------------------------------
-- | Information about the binding site of the name.
data NameInfo = Declared !ModPath !NameSource
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

                 , nNamespace :: !Namespace

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



-- | Compare two names by the way they would be displayed.
-- This is used to order names nicely when showing what's in scope
cmpNameDisplay :: NameDisp -> Name -> Name -> Ordering
cmpNameDisplay disp l r =
  case (asOrigName l, asOrigName r) of

    (Just ogl, Just ogr) -> -- XXX: uses system name info?
       case cmpText (fmtPref ogl) (fmtPref ogr) of
         EQ  -> cmpName l r
         cmp -> cmp

    (Nothing,Nothing) -> cmpName l r

    (Just ogl,Nothing) ->
       case cmpText (fmtPref ogl) (identText (nameIdent r)) of
         EQ  -> GT
         cmp -> cmp

    (Nothing,Just ogr) ->
       case cmpText (identText (nameIdent l)) (fmtPref ogr) of
         EQ  -> LT
         cmp -> cmp

  where
  cmpName xs ys  = cmpIdent (nameIdent xs) (nameIdent ys)
  cmpIdent xs ys = cmpText (identText xs) (identText ys)

      --- let pfxl = fmtModName nsl (getNameFormat nsl (nameIdent l) disp)
  fmtPref og = case getNameFormat og disp of
                 UnQualified -> ""
                 Qualified q -> modNameToText q
                 NotInScope  -> Text.pack $ show $ pp (ogModule og)

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
-- the need for parentheses.
ppName :: Name -> Doc
ppName nm =
  case asOrigName nm of
    Just og -> pp og
    Nothing -> pp (nameIdent nm)


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

nameNamespace :: Name -> Namespace
nameNamespace = nNamespace

nameInfo :: Name -> NameInfo
nameInfo  = nInfo

nameLoc :: Name -> Range
nameLoc  = nLoc

nameFixity :: Name -> Maybe Fixity
nameFixity = nFixity

-- | Primtiives must be in a top level module, at least for now.
asPrim :: Name -> Maybe PrimIdent
asPrim Name { .. } =
  case nInfo of
    Declared (TopModule m) _ -> Just $ PrimIdent m $ identText nIdent
    _                        -> Nothing

toParamInstName :: Name -> Name
toParamInstName n =
  case nInfo n of
    Declared m s -> n { nInfo = Declared (apPathRoot paramInstModName m) s }
    Parameter   -> n

asParamName :: Name -> Name
asParamName n = n { nInfo = Parameter }

asOrigName :: Name -> Maybe OrigName
asOrigName nm =
  case nInfo nm of
    Declared p _ -> Just OrigName { ogModule    = p
                                  , ogNamespace = nNamespace nm
                                  , ogName      = nIdent nm
                                  }
    Parameter    -> Nothing


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
mkDeclared ::
  Namespace -> ModPath -> NameSource -> Ident -> Maybe Fixity -> Range ->
  Supply -> (Name,Supply)
mkDeclared nNamespace m sys nIdent nFixity nLoc s =
  let (nUnique,s') = nextUnique s
      nInfo        = Declared m sys
   in (Name { .. }, s')

-- | Make a new parameter name.
mkParameter :: Namespace -> Ident -> Range -> Supply -> (Name,Supply)
mkParameter nNamespace nIdent nLoc s =
  let (nUnique,s') = nextUnique s
      nFixity      = Nothing
   in (Name { nInfo = Parameter, .. }, s')

paramModRecParam :: Name
paramModRecParam = Name { nInfo = Parameter
                        , nFixity = Nothing
                        , nIdent  = packIdent "$modParams"
                        , nLoc    = emptyRange
                        , nUnique = 0x01
                        , nNamespace = NSValue
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

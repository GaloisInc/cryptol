-- |
-- Module      :  Cryptol.ModuleSystem.Name
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
-- for the instances of RunM and BaseM
{-# LANGUAGE UndecidableInstances #-}

module Cryptol.ModuleSystem.Name (
    -- * Names
    Name(), NameInfo(..), NameSource(..)
  , nameUnique
  , nameIdent
  , mapNameIdent
  , nameInfo
  , nameSrc
  , nameLoc
  , nameFixity
  , nameNamespace
  , nameToDefPName
  , nameToPNameWithQualifiers
  , asPrim
  , asOrigName
  , nameModPath
  , nameModPathMaybe
  , nameTopModule
  , nameTopModuleMaybe
  , ppLocName
  , Namespace(..)
  , ModPath(..)
  , cmpNameDisplay

    -- ** Creation
  , mkDeclared
  , mkLocal
  , mkLocalPName
  , asLocal
  , mkModParam

    -- ** Unique Supply
  , FreshM(..), nextUniqueM
  , SupplyT(), runSupplyT, runSupply
  , Supply(), emptySupply, nextUnique
  , freshNameFor

    -- ** PrimMap
  , PrimMap(..)
  , lookupPrimDecl
  , lookupPrimType
  ) where

import           Control.DeepSeq
import qualified Data.Map as Map
import qualified Data.Monoid as M
import           Data.Functor.Identity(runIdentity)
import           GHC.Generics (Generic)
import           MonadLib
import           Prelude ()
import           Prelude.Compat
import qualified Data.Text as Text
import           Data.Char(isAlpha,toUpper)


import           Cryptol.Parser.Name (PName, NameSource(..))
import qualified Cryptol.Parser.Name as PName
import           Cryptol.Parser.Position (Range,Located(..))
import           Cryptol.Utils.Fixity
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP

data NameInfo = GlobalName NameSource OrigName
              | LocalName NameSource Namespace Ident
                deriving (Generic, NFData, Show)

-- Names -----------------------------------------------------------------------
data Name = Name { nUnique :: {-# UNPACK #-} !Int
                   -- ^ INVARIANT: this field uniquely identifies a name for one
                   -- session with the Cryptol library. Names are unique to
                   -- their binding site.

                 , nInfo :: !NameInfo

                 , nFixity :: !(Maybe Fixity)
                   -- ^ The associativity and precedence level of
                   --   infix operators.  'Nothing' indicates an
                   --   ordinary prefix operator.

                 , nLoc :: !Range
                   -- ^ Where this name was defined
                 } deriving (Generic, NFData, Show)


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
                 NotInScope  ->
                    let m = Text.pack (show (pp (ogModule og)))
                    in
                    case ogFromParam og of
                      Just q  -> m <> "::" <> Text.pack (show (pp q))
                      Nothing -> m

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
  case nInfo nm of
    GlobalName _ og -> pp og
    LocalName _ _ i -> pp i
  <.>
  withPPCfg \cfg ->
    if ppcfgShowNameUniques cfg then "_" <.> int (nameUnique nm)
                                else mempty

instance PP Name where
  ppPrec _ = ppPrefixName

instance PPName Name where
  ppNameFixity n = nameFixity n

  ppInfixName n
    | isInfixIdent (nameIdent n) = ppName n
    | otherwise           = panic "Name" [ "Non-infix name used infix"
                                         , show (nameIdent n) ]

  ppPrefixName n = optParens (isInfixIdent (nameIdent n)) (ppName n)


-- | Pretty-print a name with its source location information.
ppLocName :: Name -> Doc
ppLocName n = pp Located { srcRange = nameLoc n, thing = n }

nameUnique :: Name -> Int
nameUnique  = nUnique

nameInfo :: Name -> NameInfo
nameInfo = nInfo

nameIdent :: Name -> Ident
nameIdent n = case nInfo n of
                GlobalName _ og -> ogName og
                LocalName _ _ i   -> i

mapNameIdent :: (Ident -> Ident) -> Name -> Name
mapNameIdent f n =
  n { nInfo =
        case nInfo n of
          GlobalName x og -> GlobalName x og { ogName = f (ogName og) }
          LocalName s x i   -> LocalName s x (f i)
    }

nameNamespace :: Name -> Namespace
nameNamespace n = case nInfo n of
                    GlobalName _ og -> ogNamespace og
                    LocalName _ ns _  -> ns

nameSrc :: Name -> NameSource
nameSrc nm =
  case nameInfo nm of
    GlobalName x _ -> x
    LocalName x _ _ -> x

nameLoc :: Name -> Range
nameLoc  = nLoc

nameFixity :: Name -> Maybe Fixity
nameFixity = nFixity

-- | Compute a `PName` for the definition site corresponding to the given
-- `Name`.   Usually this is an unqualified name, but names that come
-- from module parameters are qualified with the corresponding parameter name.
nameToDefPName :: Name -> PName
nameToDefPName n =
  case nInfo n of
    GlobalName ns og -> PName.origNameToDefPName og ns
    LocalName ns _ txt -> PName.mkUnqual txt ns

-- | Compute a `PName` from `Name`, this preserves all qualifiers in the name,
-- whereas `nameToDefPName` does not.
nameToPNameWithQualifiers :: Name -> PName
nameToPNameWithQualifiers n =
  case nameInfo n of
    GlobalName ns og   -> origNameToPName og ns
    LocalName ns _ txt -> PName.mkUnqual txt ns

  where
  origNameToPName :: OrigName -> NameSource -> PName
  origNameToPName og vis =
    case modPathSplit (ogModule og) of
      (_top,[] ) -> PName.UnQual' ident vis
      (_top,ids) -> PName.Qual (packModName (map identText ids)) ident

    where
    ident = ogName og


-- | Primtives must be in a top level module, at least for now.
asPrim :: Name -> Maybe PrimIdent
asPrim n =
  case nInfo n of
    GlobalName _ og
      | TopModule m <- ogModule og, not (ogIsModParam og) ->
        Just $ PrimIdent m $ identText $ ogName og

    _ -> Nothing

asOrigName :: Name -> Maybe OrigName
asOrigName n =
  case nInfo n of
    GlobalName _ og -> Just og
    LocalName {}    -> Nothing

-- | Get the module path for the given name.
nameModPathMaybe :: Name -> Maybe ModPath
nameModPathMaybe n = ogModule <$> asOrigName n

-- | Get the module path for the given name.
-- The name should be a top-level name.
nameModPath :: Name -> ModPath
nameModPath n =
  case nameModPathMaybe n of
    Just p  -> p
    Nothing -> panic "nameModPath" [ "Not a top-level name: ", show n ]


-- | Get the name of the top-level module that introduced this name.
nameTopModuleMaybe :: Name -> Maybe ModName
nameTopModuleMaybe = fmap topModuleFor . nameModPathMaybe

-- | Get the name of the top-level module that introduced this name.
-- Works only for top-level names (i.e., that have original names)
nameTopModule :: Name -> ModName
nameTopModule = topModuleFor . nameModPath

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

runSupply :: Supply -> (forall m. FreshM m => m a) -> (a,Supply)
runSupply s m = runIdentity (runSupplyT s m)

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
-- XXX: perhaps we should simply not have such things
-- XXX: do we have these anymore?

nextUnique :: Supply -> (Int,Supply)
nextUnique (Supply n) = s' `seq` (n,s')
  where
  s' = Supply (n + 1)


-- Name Construction -----------------------------------------------------------

-- | Make a new name for a declaration.
mkDeclared ::
  Namespace -> ModPath -> NameSource -> Ident -> Maybe Fixity -> Range ->
  Supply -> (Name,Supply)
mkDeclared ns m sys ident fixity loc s = (name, s')
  where
  (u,s') = nextUnique s
  name = Name { nUnique   = u
              , nFixity   = fixity
              , nLoc      = loc
              , nInfo     = GlobalName
                              sys
                              OrigName
                                { ogNamespace = ns
                                , ogModule    = m
                                , ogName      = ident
                                , ogSource    = FromDefinition
                                , ogFromParam = Nothing
                                }
              }

-- | Make a new parameter name.
mkLocalPName :: Namespace -> PName -> Range -> Supply -> (Name,Supply)
mkLocalPName ns nm = mkLocal src ns ident
  where
  ident = PName.getIdent nm
  src   = case nm of
            PName.NewName {} -> PName.SystemName
            _                -> PName.UserName

-- | Make a new parameter name.
mkLocal :: NameSource -> Namespace -> Ident -> Range -> Supply -> (Name,Supply)
mkLocal src ns ident loc s = (name, s')
  where
  (u,s')  = nextUnique s
  name    = Name { nUnique = u
                 , nLoc    = loc
                 , nFixity = Nothing
                 , nInfo   = LocalName src ns ident
                 }

{- | Make a local name derived from the given name.
This is a bit questionable,
but it is used by the translation to SAW Core -}
asLocal :: Namespace -> Name -> Name
asLocal ns x =
  case nameInfo x of
    GlobalName src og -> x { nInfo = LocalName src ns (ogName og) }
    LocalName {}    -> x

mkModParam ::
  ModPath {- ^ Module containing the parameter -} ->
  Ident   {- ^ Name of the module parameter    -} ->
  Range   {- ^ Location                        -} ->
  Name    {- ^ Name in the signature           -} ->
  Supply -> (Name, Supply)
mkModParam own pname rng n s = (name, s')
  where
  (u,s') = nextUnique s
  name = Name { nUnique = u
              , nInfo   = GlobalName
                            PName.UserName
                            OrigName
                              { ogModule    = own
                              , ogName      = nameIdent n
                              , ogNamespace = nameNamespace n
                              , ogSource    = FromModParam
                              , ogFromParam = Just pname
                              }
              , nFixity = nFixity n
              , nLoc    = rng
              }

-- | This is used when instantiating functors
freshNameFor :: ModPath -> Name -> Supply -> (Name,Supply)
freshNameFor mpath x s = (newName, s1)
  where
  (u,s1) = nextUnique s
  newName =
    x { nUnique = u
      , nInfo =
          case nInfo x of
            GlobalName src og -> GlobalName src og { ogModule = mpath
                                                   , ogSource = FromFunctorInst }
            LocalName {} -> panic "freshNameFor" ["Unexpected local",show x]
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

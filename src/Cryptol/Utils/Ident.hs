-- |
-- Module      :  Cryptol.Utils.Ident
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.Utils.Ident
  ( -- * Module names
    ModPath(..)
  , apPathRoot
  , modPathCommon
  , modPathIsOrContains
  , topModuleFor
  , modPathSplit
  , modPathIsNormal

  , ModName
  , modNameToText
  , textToModName
  , modNameChunks
  , modNameChunksText
  , packModName
  , identToModName
  , preludeName
  , preludeReferenceName
  , undefinedModName
  , floatName
  , suiteBName
  , arrayName
  , primeECName
  , interactiveName
  , noModuleName
  , exprModName
  , modNameArg
  , modNameIfaceMod
  , modNameToNormalModName
  , modNameIsNormal

    -- * Identifiers
  , Ident
  , packIdent
  , packInfix
  , unpackIdent
  , mkIdent
  , mkInfix
  , isInfixIdent
  , nullIdent
  , identText
  , modParamIdent
  , identAnonArg
  , identAnonIfaceMod
  , identIsNormal

    -- * Namespaces
  , Namespace(..)
  , allNamespaces

    -- * Original names
  , OrigName(..)
  , OrigSource(..)
  , ogIsModParam

    -- * Identifiers for primitives
  , PrimIdent(..)
  , prelPrim
  , floatPrim
  , arrayPrim
  , suiteBPrim
  , primeECPrim
  ) where

import           Control.DeepSeq (NFData)
import           Data.Char (isSpace)
import           Data.List (unfoldr)
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.String (IsString(..))
import           GHC.Generics (Generic)

import Cryptol.Utils.Panic(panic)


--------------------------------------------------------------------------------

-- | Namespaces for names
data Namespace = NSValue | NSType | NSModule
  deriving (Generic,Show,NFData,Eq,Ord,Enum,Bounded)

allNamespaces :: [Namespace]
allNamespaces = [ minBound .. maxBound ]

-- | Idnetifies a possibly nested module
data ModPath  = TopModule ModName
              | Nested ModPath Ident
                deriving (Eq,Ord,Show,Generic,NFData)

apPathRoot :: (ModName -> ModName) -> ModPath -> ModPath
apPathRoot f path =
  case path of
    TopModule m -> TopModule (f m)
    Nested p q  -> Nested (apPathRoot f p) q

topModuleFor :: ModPath -> ModName
topModuleFor m =
  case m of
    TopModule x -> x
    Nested p _ -> topModuleFor p

-- | Compute a common prefix between two module paths, if any.
-- This is basically "anti-unification" of the two paths, where we
-- compute the longest common prefix, and the remaining differences for
-- each module.
modPathCommon :: ModPath -> ModPath -> Maybe (ModPath, [Ident], [Ident])
modPathCommon p1 p2
  | top1 == top2 = Just (findCommon (TopModule top1) as bs)
  | otherwise    = Nothing
  where
  (top1,as) = modPathSplit p1
  (top2,bs) = modPathSplit p2

  findCommon com xs ys =
    case (xs,ys) of
      (x:xs',y:ys') | x == y -> findCommon (Nested com x) xs' ys'
      _                      -> (com, xs, ys)

-- | Does the first module path contain the second?
-- This returns true if the paths are the same.
modPathIsOrContains :: ModPath -> ModPath -> Bool
modPathIsOrContains p1 p2 =
  case modPathCommon p1 p2 of
    Just (_,[],_) -> True
    _ -> False

modPathSplit :: ModPath -> (ModName, [Ident])
modPathSplit p0 = (top,reverse xs)
  where
  (top,xs) = go p0
  go p =
    case p of
      TopModule a -> (a, [])
      Nested b i  -> (a, i:bs)
        where (a,bs) = go b

modPathIsNormal :: ModPath -> Bool
modPathIsNormal p = modNameIsNormal m && all identIsNormal is
  where (m,is) = modPathSplit p


--------------------------------------------------------------------------------
-- | Top-level Module names are just text.
data ModName = ModName Text MaybeAnon
  deriving (Eq,Ord,Show,Generic)

instance NFData ModName

-- | Change a normal module name to a module name to be used for an
-- anonnymous argument.
modNameArg :: ModName -> ModName
modNameArg (ModName m fl) =
  case fl of
    NormalName        -> ModName m AnonModArgName
    AnonModArgName    -> panic "modNameArg" ["Name is not normal"]
    AnonIfaceModName  -> panic "modNameArg" ["Name is not normal"]

-- | Change a normal module name to a module name to be used for an
-- anonnymous interface.
modNameIfaceMod :: ModName -> ModName
modNameIfaceMod (ModName m fl) =
  case fl of
    NormalName        -> ModName m AnonIfaceModName
    AnonModArgName    -> panic "modNameIfaceMod" ["Name is not normal"]
    AnonIfaceModName  -> panic "modNameIfaceMod" ["Name is not normal"]

-- | This is used when we check that the name of a module matches the
-- file where it is defined.
modNameToNormalModName :: ModName -> ModName
modNameToNormalModName (ModName t _) = ModName t NormalName

modNameToText :: ModName -> Text
modNameToText (ModName x fl) = maybeAnonText fl x

-- | This is useful when we want to hide anonymous modules.
modNameIsNormal :: ModName -> Bool
modNameIsNormal (ModName _ fl) = isNormal fl

-- | Make a normal module name out of text.
textToModName :: T.Text -> ModName
textToModName txt = ModName txt NormalName

-- | Break up a module name on the separators, `Text` version.
modNameChunksText :: ModName -> [T.Text]
modNameChunksText (ModName x fl) = unfoldr step x
  where
  step str
    | T.null str = Nothing
    | otherwise  =
      case T.breakOn modSep str of
        (a,b)
          | T.null b  -> Just (maybeAnonText fl str, b)
          | otherwise -> Just (a,T.drop (T.length modSep) b)

-- | Break up a module name on the separators, `String` version
modNameChunks :: ModName -> [String]
modNameChunks = map T.unpack . modNameChunksText

packModName :: [T.Text] -> ModName
packModName strs = textToModName (T.intercalate modSep (map trim strs))
  where
  -- trim space off of the start and end of the string
  trim str = T.dropWhile isSpace (T.dropWhileEnd isSpace str)

identToModName :: Ident -> ModName
identToModName (Ident _ anon txt) = ModName txt anon

modSep :: T.Text
modSep  = "::"

preludeName :: ModName
preludeName  = packModName ["Cryptol"]

undefinedModName :: ModName
undefinedModName = packModName ["Undefined module"]

preludeReferenceName :: ModName
preludeReferenceName = packModName ["Cryptol","Reference"]

floatName :: ModName
floatName = packModName ["Float"]

arrayName :: ModName
arrayName  = packModName ["Array"]

suiteBName :: ModName
suiteBName = packModName ["SuiteB"]

primeECName :: ModName
primeECName = packModName ["PrimeEC"]

interactiveName :: ModName
interactiveName  = packModName ["<interactive>"]

noModuleName :: ModName
noModuleName = packModName ["<none>"]

exprModName :: ModName
exprModName = packModName ["<expr>"]


--------------------------------------------------------------------------------
-- | Identifies an entitiy
data OrigName = OrigName
  { ogNamespace :: Namespace
  , ogModule    :: ModPath
  , ogSource    :: OrigSource
  , ogName      :: Ident
  , ogFromParam :: !(Maybe Ident)
    -- ^ Does this name come from a module parameter
  } deriving (Eq,Ord,Show,Generic,NFData)

-- | Describes where a top-level name came from
data OrigSource =
    FromDefinition
  | FromFunctorInst
  | FromModParam
    deriving (Eq,Ord,Show,Generic,NFData)

-- | Returns true iff the 'ogSource' of the given 'OrigName' is 'FromModParam'
ogIsModParam :: OrigName -> Bool
ogIsModParam og = case ogSource og of
                      FromModParam -> True
                      _ -> False


--------------------------------------------------------------------------------

{- | The type of identifiers.
  * The boolean flag indicates whether or not they're infix operators.
    The boolean is present just as cached information from the lexer,
    and never used during comparisons.
  * The MaybeAnon indicates if this is an anonymous name  -}
data Ident = Ident Bool MaybeAnon T.Text
             deriving (Show,Generic)

instance Eq Ident where
  a == b = compare a b == EQ
  a /= b = compare a b /= EQ

instance Ord Ident where
  compare (Ident _ mb1 i1) (Ident _ mb2 i2) = compare (mb1,i1) (mb2,i2)

instance IsString Ident where
  fromString str = mkIdent (T.pack str)

instance NFData Ident

-- | Make a normal (i.e., not anonymous) identifier
packIdent :: String -> Ident
packIdent  = mkIdent . T.pack

-- | Make a normal (i.e., not anonymous) identifier
packInfix :: String -> Ident
packInfix  = mkInfix . T.pack

unpackIdent :: Ident -> String
unpackIdent  = T.unpack . identText

-- | Make a normal (i.e., not anonymous) identifier
mkIdent :: T.Text -> Ident
mkIdent  = Ident False NormalName

mkInfix :: T.Text -> Ident
mkInfix  = Ident True NormalName

isInfixIdent :: Ident -> Bool
isInfixIdent (Ident b _ _) = b

nullIdent :: Ident -> Bool
nullIdent = T.null . identText

identText :: Ident -> T.Text
identText (Ident _ mb t) = maybeAnonText mb t

modParamIdent :: Ident -> Ident
modParamIdent (Ident x a t) =
  Ident x a (T.append (T.pack "module parameter ") t)

-- | Make an anonymous identifier for the module corresponding to
-- a `where` block in a functor instantiation.
identAnonArg :: Ident -> Ident
identAnonArg (Ident b _ txt) = Ident b AnonModArgName txt

-- | Make an anonymous identifier for the interface corresponding to
-- a `parameter` declaration.
identAnonIfaceMod :: Ident -> Ident
identAnonIfaceMod (Ident b _ txt) = Ident b AnonIfaceModName txt

identIsNormal :: Ident -> Bool
identIsNormal (Ident _ mb _) = isNormal mb

--------------------------------------------------------------------------------

-- | Information about anonymous names.
data MaybeAnon = NormalName       -- ^ Not an anonymous name.
               | AnonModArgName   -- ^ Anonymous module (from `where`)
               | AnonIfaceModName -- ^ Anonymous interface (from `parameter`)
  deriving (Eq,Ord,Show,Generic)

instance NFData MaybeAnon

-- | Modify a name, if it is a nonymous
maybeAnonText :: MaybeAnon -> Text -> Text
maybeAnonText mb txt =
  case mb of
    NormalName       -> txt
    AnonModArgName   -> "`where` argument of " <> txt
    AnonIfaceModName -> "`parameter` interface of " <> txt

isNormal :: MaybeAnon -> Bool
isNormal mb =
  case mb of
    NormalName -> True
    _          -> False




--------------------------------------------------------------------------------

{- | A way to identify primitives: we used to use just 'Ident', but this
isn't good anymore as now we have primitives in multiple modules.
This is used as a key when we need to lookup details about a specific
primitive.  Also, this is intended to mostly be used internally, so
we don't store the fixity flag of the `Ident` -}
data PrimIdent = PrimIdent ModName T.Text
  deriving (Eq,Ord,Show,Generic)

-- | A shortcut to make (non-infix) primitives in the prelude.
prelPrim :: T.Text -> PrimIdent
prelPrim = PrimIdent preludeName

floatPrim :: T.Text -> PrimIdent
floatPrim = PrimIdent floatName

suiteBPrim :: T.Text -> PrimIdent
suiteBPrim = PrimIdent suiteBName

primeECPrim :: T.Text -> PrimIdent
primeECPrim = PrimIdent primeECName

arrayPrim :: T.Text -> PrimIdent
arrayPrim = PrimIdent arrayName

instance NFData PrimIdent

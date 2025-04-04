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
  , mainModName
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
  , modNamesMatch
  , modNameIsNormal

    -- * Identifiers
  , Ident
  , packIdent
  , packInfix
  , unpackIdent
  , mkIdent
  , mkInfix
  , isInfixIdent
  , isUpperIdent
  , isAnonIfaceModIdnet
  , nullIdent
  , identText
  , identAnonArg
  , identAnonIfaceMod
  , identAnonInstImport
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
import           Data.Char (isSpace,isUpper)
import           Data.List (unfoldr)
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.String (IsString(..))
import           GHC.Generics (Generic)

import Cryptol.Utils.Panic(panic)


--------------------------------------------------------------------------------

-- | Namespaces for names
data Namespace = NSValue
               | NSConstructor -- ^ This is for enum and newtype constructors

               | NSType
               | NSModule
  deriving (Generic,Show,NFData,Eq,Ord,Enum,Bounded)

allNamespaces :: [Namespace]
allNamespaces = [ minBound .. maxBound ]

-- | Identifies a possibly nested module
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
             | ModMain FilePath
  deriving (Eq,Ord,Show,Generic)

instance NFData ModName

-- | Change a normal module name to a module name to be used for an
-- anonnymous argument.  The first two ints are the line and column of the
-- name, which are used for name disambiguation.
modNameArg :: Int -> Int -> ModName -> ModName
modNameArg l c (ModName m fl) =
  case fl of
    NormalName        -> ModName m (AnonModArgName l c)
    AnonModArgName {} -> panic "modNameArg" ["Name is not normal"]
    AnonIfaceModName  -> panic "modNameArg" ["Name is not normal", "AnonModArgName" ]
    AnonInstImport {} -> panic "modNameArg" ["Name is not normal", "AnonIfaceModName" ]
modNameArg _ _ (ModMain _) = panic "modNameArg" ["Name is not normal", "AnonInstImport"]

-- | Change a normal module name to a module name to be used for an
-- anonnymous interface.
modNameIfaceMod :: ModName -> ModName
modNameIfaceMod (ModName m fl) =
  case fl of
    NormalName        -> ModName m AnonIfaceModName
    AnonModArgName {} -> panic "modNameIfaceMod" ["Name is not normal", "AnonModArgName"]
    AnonIfaceModName  -> panic "modNameIfaceMod" ["Name is not normal", "AnonIfaceModName" ]
    AnonInstImport {} -> panic "modNameIfaceMod" ["Name is not normal", "AnonInstImport" ]
modNameIfaceMod (ModMain _) = panic "modNameIfaceMod" ["Name is not normal"]

modNameToNormalModName :: ModName -> ModName
modNameToNormalModName (ModName t _) = ModName t NormalName
modNameToNormalModName (ModMain p) = ModMain p

-- | This is used when we check that the name of a module matches the
-- file where it is defined.
modNamesMatch :: ModName -> ModName -> Bool
modNamesMatch (ModName a _) (ModName b _) = a == b
modNamesMatch (ModMain a) (ModMain b) = a == b
modNamesMatch _ _ = False

modNameToText :: ModName -> Text
modNameToText (ModName x fl) = maybeAnonText fl x
modNameToText (ModMain _) = "Main"

-- | This is useful when we want to hide anonymous modules.
modNameIsNormal :: ModName -> Bool
modNameIsNormal (ModName _ fl) = isNormal fl
modNameIsNormal (ModMain _) = False

-- | Make a normal module name out of text. This function should not
-- be used to build a @Main@ module name. See 'mainModName'.
textToModName :: T.Text -> ModName
textToModName txt = ModName txt NormalName

mainModName :: FilePath -> ModName
mainModName = ModMain

-- | Break up a module name on the separators, `Text` version.
-- For the main module this will forget the filename that
-- corresponds to this module and will only report @["Main"]@
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
modNameChunksText (ModMain _) =  ["Main"]

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

isUpperIdent :: Ident -> Bool
isUpperIdent (Ident _ mb t) =
  case mb of
    NormalName | Just (c,_) <- T.uncons t -> isUpper c
    _ -> False

-- | Is this an ident for an anonymous module interface
-- (i.e., a `parameter` block)?
isAnonIfaceModIdnet :: Ident -> Bool
isAnonIfaceModIdnet (Ident _ ty _) =
  case ty of
    AnonIfaceModName -> True
    _                -> False

nullIdent :: Ident -> Bool
nullIdent = T.null . identText

identText :: Ident -> T.Text
identText (Ident _ mb t) = maybeAnonText mb t

-- | Make an anonymous identifier for the module corresponding to
-- a `where` block in a functor instantiation. 
-- The two ints are the line and column of the definition site.
identAnonArg :: Int -> Int -> Ident
identAnonArg l c = Ident False (AnonModArgName l c) ""

-- | Make an anonymous identifier for the interface corresponding to
-- a `parameter` declaration.
identAnonIfaceMod :: Ident -> Ident
identAnonIfaceMod (Ident b _ txt) = Ident b AnonIfaceModName txt

-- | Make an anonymous identifier for an instantiation in an import.
-- The two ints are the line and column of the definition site.
identAnonInstImport :: Int -> Int -> Ident
identAnonInstImport l c = Ident False (AnonInstImport l c) ""

identIsNormal :: Ident -> Bool
identIsNormal (Ident _ mb _) = isNormal mb

--------------------------------------------------------------------------------

-- | Information about anonymous names.
data MaybeAnon = NormalName       -- ^ Not an anonymous name.
               | AnonModArgName Int Int-- ^ Anonymous module (line,column) (from `where`)
               | AnonIfaceModName -- ^ Anonymous interface (from `parameter`)
               | AnonInstImport Int Int 
                 -- ^ Anonymous instance import (line, column)
  deriving (Eq,Ord,Show,Generic)

instance NFData MaybeAnon

-- | Modify a name, if it is a nonymous.
-- If we change this, please update the reference manual as well, so that
-- folks know how to refer to these in external tools.
maybeAnonText :: MaybeAnon -> Text -> Text
maybeAnonText mb txt =
  case mb of
    NormalName -> txt
    AnonModArgName l c
      | T.null txt -> "where_at__" <> suff l c
      | otherwise  -> txt <> "__where"
    AnonIfaceModName    -> txt <> "__parameter"
    AnonInstImport l c  -> "import_at__" <> suff l c
  where
  suff l c = T.pack (if c == 1 then show l else show l ++ "_" ++ show c)


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

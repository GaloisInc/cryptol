{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}

-- | Generate C header files from foreign declarations.
module Cryptol.Eval.FFI.GenHeader
  ( generateForeignHeader
  ) where

import           Control.Monad.Writer.Strict
import           Data.Bifunctor
import           Data.Functor
import           Data.List
import           Data.Set                      (Set)
import qualified Data.Set                      as Set
import           Language.C99.Pretty           as C
import qualified Language.C99.Simple           as C
import qualified Text.PrettyPrint              as Pretty

import           Cryptol.ModuleSystem.Name
import           Cryptol.TypeCheck.FFI.FFIType
import           Cryptol.TypeCheck.Type
import           Cryptol.Utils.Ident
import           Cryptol.Utils.RecordMap

-- | @Include foo@ represents an include statement @#include <foo>@
newtype Include = Include String deriving (Eq, Ord)

-- | The monad for generating headers. We keep track of which headers we need to
-- include and add them to the output at the end.
type GenHeaderM = Writer (Set Include)

-- | Generate a C header file from the given foreign declarations.
generateForeignHeader :: [(Name, FFIFunType)] -> String
generateForeignHeader decls =
  unlines (map renderInclude $ Set.toAscList incs)
  ++ Pretty.render (C.pretty $ C.translate (C.TransUnit cdecls []))
  where (cdecls, incs) = runWriter $ traverse convertFun decls

renderInclude :: Include -> String
renderInclude (Include inc) = "#include <" ++ inc ++ ">"

-- | The "direction" of a parameter (input or output).
data ParamDir = In | Out

-- | The result of converting a Cryptol type into its C representation.
data ConvertResult
  = Direct C.Type -- ^ A type that can be directly returned if it is a return
                  -- type and passed as a single parameter if it is a Cryptol
                  -- parameter type.
  | Params [C.Param] -- ^ A type that is turned into a number of parameters,
                     -- for both Cryptol parameter and return type cases.

-- | Convert a Cryptol foreign declaration into a C function declaration.
convertFun :: (Name, FFIFunType) -> GenHeaderM C.Decln
convertFun (fName, FFIFunType {..}) = do
  typeParams <- traverse convertTypeParam ffiTParams
  -- Name the input args in0, in1, etc
  let inPrefixes =
        case ffiArgTypes of
          [_] -> ["in"]
          _   -> ["in" ++ show @Integer i | i <- [0..]]
  inParams <- convertMultiType In $ zip inPrefixes ffiArgTypes
  (retType, outParams) <- convertType Out ffiRetType
    <&> \case
      Direct u  -> (u, [])
      -- Name the output arg out
      Params ps -> (C.TypeSpec C.Void, map (prefixParam "out") ps)
  let renameParam names (C.Param u name) =
        (Set.insert name' names, C.Param u name')
        where name' = until (`Set.notMember` names) (++ "_") name
      -- Avoid possible name collisions
      params = snd $ mapAccumL renameParam Set.empty $
        typeParams ++ inParams ++ outParams
  pure $ C.FunDecln Nothing retType (unpackIdent $ nameIdent fName) params

-- | Convert a Cryptol type parameter to a C value parameter.
convertTypeParam :: TParam -> GenHeaderM C.Param
convertTypeParam tp = (`C.Param` name) <$> sizeT
  where -- We use the name of the type parameter, which should always exist
        -- since signatures are required
        name = maybe "" (unpackIdent . nameIdent) $ tpName tp

-- | Convert a Cryptol parameter or return type to C.
convertType :: ParamDir -> FFIType -> GenHeaderM ConvertResult
convertType _ FFIBool = Direct <$> uint8T
convertType _ (FFIBasic t) = Direct <$> convertBasicType t
convertType _ (FFIArray _ t) = do
  u <- convertBasicType t
  pure $ Params [C.Param (C.Ptr u) ""]
convertType dir (FFITuple ts) = Params <$> convertMultiType dir
  -- We name the tuple components using their indices
  (zip (map (componentSuffix . show @Integer) [0..]) ts)
convertType dir (FFIRecord tMap) = Params <$> convertMultiType dir
  (map (first (componentSuffix . unpackIdent)) $ displayFields tMap)

-- | Convert many Cryptol types, each associated with a prefix, to C parameters
-- named with their prefixes.
convertMultiType :: ParamDir -> [(C.Ident, FFIType)] -> GenHeaderM [C.Param]
convertMultiType dir = fmap concat . traverse \(prefix, t) ->
  convertType dir t
    <&> \case
      Direct u -> [C.Param u' prefix]
        where u' = case dir of
                In  -> u
                -- Turn direct return types into pointer out parameters
                Out -> C.Ptr u
      Params ps -> map (prefixParam prefix) ps

-- | Convert a basic Cryptol FFI type to a C type.
convertBasicType :: FFIBasicType -> GenHeaderM C.Type
convertBasicType (FFIWord _ s) =
  case s of
    FFIWord8  -> uint8T
    FFIWord16 -> uint16T
    FFIWord32 -> uint32T
    FFIWord64 -> uint64T
convertBasicType (FFIFloat _ _ s) =
  case s of
    FFIFloat32 -> pure $ C.TypeSpec C.Float
    FFIFloat64 -> pure $ C.TypeSpec C.Double

prefixParam :: C.Ident -> C.Param -> C.Param
prefixParam pre (C.Param u name) = C.Param u (pre ++ name)

-- | Create a suffix corresponding to some component name of some larger type.
componentSuffix :: String -> C.Ident
componentSuffix = ('_' :)

sizeT, uint8T, uint16T, uint32T, uint64T :: GenHeaderM C.Type
sizeT = typedefFromInclude stddefH "size_t"
uint8T = typedefFromInclude stdintH "uint8_t"
uint16T = typedefFromInclude stdintH "uint16_t"
uint32T = typedefFromInclude stdintH "uint32_t"
uint64T = typedefFromInclude stdintH "uint64_t"

stddefH, stdintH :: Include
stddefH = Include "stddef.h"
stdintH = Include "stdint.h"

-- | Return a type with the given name, included from some header file.
typedefFromInclude :: Include -> C.Ident -> GenHeaderM C.Type
typedefFromInclude inc u = do
  tell $ Set.singleton inc
  pure $ C.TypeSpec $ C.TypedefName u

{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}

module Cryptol.Eval.FFI.GenHeader
  ( generateForeignHeader
  ) where

import           Control.Monad.Writer.Strict
import           Data.Bifunctor
import           Data.Functor
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

newtype Include = Include String deriving (Eq, Ord)
type GenHeaderM = Writer (Set Include)

generateForeignHeader :: [(Name, FFIFunType)] -> String
generateForeignHeader decls =
  unlines (map renderInclude $ Set.toAscList incs)
  ++ Pretty.render (C.pretty $ C.translate (C.TransUnit cdecls []))
  where (cdecls, incs) = runWriter $ traverse convertFun decls

renderInclude :: Include -> String
renderInclude (Include inc) = "#include <" ++ inc ++ ">"

data ParamDir = In | Out
data ConvertResult = Direct C.Type | Params [C.Param]

convertFun :: (Name, FFIFunType) -> GenHeaderM C.Decln
convertFun (name, FFIFunType {..}) = do
  typeParams <- traverse convertTypeParam ffiTParams
  let inPrefixes =
        case ffiArgTypes of
          [_] -> ["in"]
          _   -> ["in" ++ show @Integer i | i <- [0..]]
  inParams <- convertMultiType In $ zip inPrefixes ffiArgTypes
  (retType, outParams) <- convertType Out ffiRetType
    <&> \case
      Direct u  -> (u, [])
      Params ps -> (C.TypeSpec C.Void, map (prefixParam "out") ps)
  let typeParamNames = map paramName typeParams
      valParams = until (not . any ((`elem` typeParamNames) . paramName))
        (map (prefixParam "_")) (inParams ++ outParams)
  pure $ C.FunDecln Nothing retType (unpackIdent $ nameIdent name) $
    typeParams ++ valParams

convertTypeParam :: TParam -> GenHeaderM C.Param
convertTypeParam tp = (`C.Param` name) <$> sizeT
  where name = maybe "" (unpackIdent . nameIdent) $ tpName tp

convertType :: ParamDir -> FFIType -> GenHeaderM ConvertResult
convertType _ FFIBool = Direct <$> uint8T
convertType _ (FFIBasic t) = Direct <$> convertBasicType t
convertType _ (FFIArray _ t) = do
  u <- convertBasicType t
  pure $ Params [C.Param (C.Ptr u) ""]
convertType dir (FFITuple ts) = Params <$> convertMultiType dir
  (zip (map (componentSuffix . show @Integer) [0..]) ts)
convertType dir (FFIRecord tMap) = Params <$> convertMultiType dir
  (map (first (componentSuffix . unpackIdent)) $ displayFields tMap)

convertMultiType :: ParamDir -> [(C.Ident, FFIType)] -> GenHeaderM [C.Param]
convertMultiType dir = fmap concat . traverse \(prefix, t) ->
  convertType dir t
    <&> \case
      Direct u -> [C.Param u' prefix]
        where u' = case dir of
                In  -> u
                Out -> C.Ptr u
      Params ps -> map (prefixParam prefix) ps

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

paramName :: C.Param -> C.Ident
paramName (C.Param _ name) = name

prefixParam :: C.Ident -> C.Param -> C.Param
prefixParam pre (C.Param u name) = C.Param u (pre ++ name)

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

typedefFromInclude :: Include -> C.Ident -> GenHeaderM C.Type
typedefFromInclude inc u = do
  tell $ Set.singleton inc
  pure $ C.TypeSpec $ C.TypedefName u

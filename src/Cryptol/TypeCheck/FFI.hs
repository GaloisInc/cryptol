{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE Safe    #-}

-- | Checking and conversion of 'Type's to 'FFIType's.
module Cryptol.TypeCheck.FFI
  ( toFFIFunType
  ) where

import           Data.Bifunctor
import           Data.Containers.ListUtils
import           Data.Either

import           Cryptol.Parser.AST(ForeignMode(..))
import           Cryptol.TypeCheck.FFI.Error
import           Cryptol.TypeCheck.FFI.FFIType
import           Cryptol.TypeCheck.SimpType
import           Cryptol.TypeCheck.Type
import           Cryptol.TypeCheck.AST(FFI(..))
import           Cryptol.Utils.RecordMap
import           Cryptol.Utils.Types

-- | Convert a 'Schema' to a 'FFIFunType', along with any 'Prop's that must be
-- satisfied for the 'FFIFunType' to be valid.
toFFIFunType :: ForeignMode -> Schema -> Either FFITypeError ([Prop], FFI)
toFFIFunType how (Forall params _ t) =

  case how of
    ForeignAbstract -> checkForeignAbstract params t
    ForeignC ->
       -- Remove all type synonyms and simplify the type before processing it
       case go $ tRebuild' False t of
         Just (Right (props, fft)) -> Right
           -- Remove duplicate constraints
           (nubOrd $ map (fin . TVar . TVBound) params ++ props, CallC fft)
         Just (Left errs) -> Left $ FFITypeError t $ FFIBadComponentTypes errs
         Nothing -> Left $ FFITypeError t FFINotFunction
  where go (TCon (TC TCFun) [argType, retType]) = Just
          case toFFIType argType of
            Right (ps, ffiArgType) ->
              case go retType of
                Just (Right (ps', ffiFunType)) -> Right
                  ( ps ++ ps'
                  , ffiFunType
                      { ffiArgTypes = ffiArgType : ffiArgTypes ffiFunType } )
                Just (Left errs) -> Left errs
                Nothing ->
                  case toFFIType retType of
                    Right (ps', ffiRetType) -> Right
                      ( ps ++ ps'
                      , FFIFunType
                          { ffiTParams = params
                          , ffiArgTypes = [ffiArgType], .. } )
                    Left err -> Left [err]
            Left err -> Left
              case go retType of
                Just (Right _) -> [err]
                Just (Left errs) -> err : errs
                Nothing ->
                  case toFFIType retType of
                    Right _   -> [err]
                    Left err' -> [err, err']
        go _ = Nothing

-- | Convert a 'Type' to a 'FFIType', along with any 'Prop's that must be
-- satisfied for the 'FFIType' to be valid.
toFFIType :: Type -> Either FFITypeError ([Prop], FFIType)
toFFIType t =
  case t of
    TCon (TC TCBit) [] -> Right ([], FFIBool)
    (toFFIBasicType -> Just r) -> (\fbt -> ([], FFIBasic fbt)) <$> r
    TCon (TC TCSeq) _ ->
      (\(szs, fbt) -> (map fin szs, FFIArray szs fbt)) <$> go t
      where go (toFFIBasicType -> Just r) =
              case r of
                Right fbt -> Right ([], fbt)
                Left err  -> Left $ FFITypeError t $ FFIBadComponentTypes [err]
            go (TCon (TC TCSeq) [sz, ty]) = first (sz:) <$> go ty
            go _ = Left $ FFITypeError t FFIBadArrayType
    TCon (TC (TCTuple _)) ts ->
      case partitionEithers $ map toFFIType ts of
        ([], unzip -> (pss, fts)) -> Right (concat pss, FFITuple fts)
        (errs, _) -> Left $ FFITypeError t $ FFIBadComponentTypes errs
    TRec tMap ->
      case sequence resMap of
        Right resMap' -> Right $ FFIRecord <$>
          recordMapAccum (\ps (ps', ft) -> (ps' ++ ps, ft)) [] resMap'
        Left _ -> Left $ FFITypeError t $
          FFIBadComponentTypes $ lefts $ displayElements resMap
      where resMap = fmap toFFIType tMap
    _ -> Left $ FFITypeError t FFIBadType

-- | Convert a 'Type' to a 'FFIBasicType', returning 'Nothing' if it isn't a
-- basic type and 'Left' if it is but there was some other issue with it.
toFFIBasicType :: Type -> Maybe (Either FFITypeError FFIBasicType)
toFFIBasicType t =
  case t of
    TCon (TC TCSeq) [TCon (TC (TCNum n)) [], TCon (TC TCBit) []]
      | n <= 8 -> word FFIWord8
      | n <= 16 -> word FFIWord16
      | n <= 32 -> word FFIWord32
      | n <= 64 -> word FFIWord64
      | otherwise -> Just $ Left $ FFITypeError t FFIBadWordSize
      where word = Just . Right . FFIBasicVal . FFIWord n
    TCon (TC TCFloat) [TCon (TC (TCNum e)) [], TCon (TC (TCNum p)) []]
      | (e, p) == float32ExpPrec -> float FFIFloat32
      | (e, p) == float64ExpPrec -> float FFIFloat64
      | otherwise -> Just $ Left $ FFITypeError t FFIBadFloatSize
      where float = Just . Right . FFIBasicVal . FFIFloat e p
    TCon (TC TCInteger) [] -> integer Nothing
    TCon (TC TCIntMod) [n] -> integer $ Just n
    TCon (TC TCRational) [] -> Just $ Right $ FFIBasicRef FFIRational
    _ -> Nothing
  where integer = Just . Right . FFIBasicRef . FFIInteger

fin :: Type -> Prop
fin t = TCon (PC PFin) [t]


-- XXX: eliminate stuff we know will not work at runtime
checkForeignAbstract :: [TParam] -> Type -> Either FFITypeError ([Prop], FFI)
checkForeignAbstract params t =
  Right
  ( []
  , CallAbstract
      FFIFunType { ffiTParams = params, ffiArgTypes = args, ffiRetType = res }
  )
  where
  (args,res) = go t
  go ty =
    case tIsFun ty of
      Just (a,r) ->
        let (bs,r1) = go r
        in (a:bs,r1)
      Nothing -> ([],ty)
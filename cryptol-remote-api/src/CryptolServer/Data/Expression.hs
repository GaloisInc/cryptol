{-# OPTIONS_GHC -fno-warn-type-defaults -Wno-missing-deriving-strategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Data.Expression
  ( module CryptolServer.Data.Expression
  ) where

import Control.Applicative
import Control.Exception (throwIO)
import Control.Monad.IO.Class
import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as Base64
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Scientific as Sc
import Data.Text (Text, pack)
import qualified Data.Text as T
import Data.Traversable
import qualified Data.Vector as V
import Data.Text.Encoding (encodeUtf8)
import Numeric (showHex)

import Cryptol.Backend.Monad
import Cryptol.Backend.Concrete hiding (Concrete)
import qualified Cryptol.Backend.Concrete as C
import Cryptol.Backend.SeqMap (enumerateSeqMap)
import Cryptol.Backend.WordValue (asWordVal)

import Cryptol.Eval (evalSel)
import Cryptol.Eval.Concrete (Value)
import Cryptol.Eval.Type (TValue(..), tValTy)
import Cryptol.Eval.Value (GenValue(..))


import Cryptol.Parser
import Cryptol.Parser.AST (Bind(..), BindDef(..), Decl(..), Expr(..), Named(Named), TypeInst(NamedInst), Type(..), PName(..), Literal(..), NumInfo(..), Type,
          ExportType(..))
import Cryptol.Parser.Position (Located(..), emptyRange)
import Cryptol.Parser.Selector
import Cryptol.Utils.Ident
import Cryptol.Utils.RecordMap (recordFromFields, canonicalFields)

import Argo
import CryptolServer
import CryptolServer.Exceptions
import CryptolServer.Data.Type

data Encoding = Base64 | Hex
  deriving (Eq, Show, Ord)

instance JSON.FromJSON Encoding where
  parseJSON =
    withText "encoding" $
    \case
      "hex"    -> pure Hex
      "base64" -> pure Base64
      _        -> empty

data LetBinding =
  LetBinding
  { argDefName :: !Text
  , argDefVal  :: !Expression
  }
  deriving (Eq, Show)

instance JSON.FromJSON LetBinding where
  parseJSON =
    withObject "let binding" $ \o ->
      LetBinding <$> o .: "name" <*> o .: "definition"

instance JSON.ToJSON LetBinding where
  toJSON (LetBinding x def) =
    object [ "name" .= x
           , "definition" .= def
           ]

data Expression =
    Bit !Bool
  | Unit
  | Num !Encoding !Text !Integer -- ^ data and bitwidth
  | Record !(HashMap Text Expression)
  | Sequence ![Expression]
  | Tuple ![Expression]
  | Integer !Integer
  | IntegerModulo !Integer !Integer -- ^ value, modulus
  | Concrete !Text
  | Let ![LetBinding] !Expression
  | Application !Expression !(NonEmpty Expression)
  | TypeApplication !Expression !TypeArguments
  deriving (Eq, Show)

newtype TypeArguments = TypeArguments (Map Ident JSONPType)
  deriving (Eq, Show) via Map Ident (Type PName)

data ExpressionTag =
    TagNum | TagRecord | TagSequence | TagTuple | TagUnit | TagLet | TagApp | TagTypeApp | TagIntMod

instance JSON.FromJSON ExpressionTag where
  parseJSON =
    withText "tag" $
    \case
      "bits"           -> pure TagNum
      "unit"           -> pure TagUnit
      "record"         -> pure TagRecord
      "sequence"       -> pure TagSequence
      "tuple"          -> pure TagTuple
      "let"            -> pure TagLet
      "call"           -> pure TagApp
      "instantiate"    -> pure TagTypeApp
      "integer modulo" -> pure TagIntMod
      _                -> empty

instance JSON.ToJSON ExpressionTag where
  toJSON TagNum      = "bits"
  toJSON TagRecord   = "record"
  toJSON TagSequence = "sequence"
  toJSON TagTuple    = "tuple"
  toJSON TagUnit     = "unit"
  toJSON TagLet      = "let"
  toJSON TagApp      = "call"
  toJSON TagTypeApp  = "instantiate"
  toJSON TagIntMod   = "integer modulo"

instance JSON.FromJSON TypeArguments where
  parseJSON =
    withObject "type arguments" $ \o ->
      TypeArguments . Map.fromList <$>
        traverse elt (HM.toList o)
    where
      elt (name, ty) = (mkIdent name,) <$> parseJSON ty

instance JSON.FromJSON Expression where
  parseJSON v = bool v <|> integer v <|> concrete v <|> obj v
    where
      bool =
        withBool "boolean" $ pure . Bit
      integer =
        -- Note: this means that we should not expose this API to the
        -- public, but only to systems that will validate input
        -- integers. Otherwise, they can use this to allocate a
        -- gigantic integer that fills up all memory.
        withScientific "integer" $ \s ->
          case Sc.floatingOrInteger s of
            Left _fl -> empty
            Right i -> pure (Integer i)
      concrete =
        withText "concrete syntax" $ pure . Concrete

      obj =
        withObject "argument" $
        \o -> o .: "expression" >>=
              \case
                TagUnit -> pure Unit
                TagNum ->
                  do enc <- o .: "encoding"
                     Num enc <$> o .: "data" <*> o .: "width"
                TagRecord ->
                  do fields <- o .: "data"
                     flip (withObject "record data") fields $
                       \fs -> Record <$> traverse parseJSON fs
                TagSequence ->
                  do contents <- o .: "data"
                     flip (withArray "sequence") contents $
                       \s -> Sequence . V.toList <$> traverse parseJSON s
                TagTuple ->
                  do contents <- o .: "data"
                     flip (withArray "tuple") contents $
                       \s -> Tuple . V.toList <$> traverse parseJSON s
                TagLet ->
                  Let <$> o .: "binders" <*> o .: "body"
                TagApp ->
                  Application <$> o .: "function" <*> o .: "arguments"
                TagTypeApp ->
                  TypeApplication <$> o .: "generic" <*> o .: "arguments"
                TagIntMod ->
                  IntegerModulo <$> o .: "integer" <*> o .: "modulus"

instance ToJSON Encoding where
  toJSON Hex = String "hex"
  toJSON Base64 = String "base64"

instance JSON.ToJSON Expression where
  toJSON Unit = object [ "expression" .= TagUnit ]
  toJSON (Bit b) = JSON.Bool b
  toJSON (Integer i) = JSON.Number (fromInteger i)
  toJSON (IntegerModulo i n) =
    object [ "expression" .= TagIntMod
           , "integer" .= JSON.Number (fromInteger i)
           , "modulus" .= JSON.Number (fromInteger n)
           ]
  toJSON (Concrete expr) = toJSON expr
  toJSON (Num enc dat w) =
    object [ "expression" .= TagNum
           , "data" .= String dat
           , "encoding" .= enc
           , "width" .= w
           ]
  toJSON (Record fields) =
    object [ "expression" .= TagRecord
           , "data" .= object [ fieldName .= toJSON val
                              | (fieldName, val) <- HM.toList fields
                              ]
           ]
  toJSON (Sequence elts) =
    object [ "expression" .= TagSequence
           , "data" .= Array (V.fromList (map toJSON elts))
           ]
  toJSON (Tuple projs) =
    object [ "expression" .= TagTuple
           , "data" .= Array (V.fromList (map toJSON projs))
           ]
  toJSON (Let binds body) =
    object [ "expression" .= TagLet
           , "binders" .= Array (V.fromList (map toJSON binds))
           , "body" .= toJSON body
           ]
  toJSON (Application fun args) =
    object [ "expression" .= TagApp
           , "function" .= fun
           , "arguments" .= args
           ]
  toJSON (TypeApplication gen _args) =
    -- It would be dead code to do anything here, as type
    -- instantiations are not values. This code is called only as part
    -- of translating values (e.g. from "evaluate expression"). So we
    -- just fall through, rather than writing complicated code to
    -- serialize Type PName that never gets called and just bitrots.
    toJSON gen


decode :: (Argo.Method m, Monad m) => Encoding -> Text -> m Integer
decode Base64 txt =
  let bytes = encodeUtf8 txt
  in
    case Base64.decode bytes of
      Left err ->
        Argo.raise (invalidBase64 bytes err)
      Right decoded -> return $ bytesToInt decoded
decode Hex txt =
  squish <$> traverse hexDigit (T.unpack txt)
  where
    squish = foldl (\acc i -> (acc * 16) + i) 0

hexDigit :: (Argo.Method m, Monad m) => Num a => Char -> m a
hexDigit '0' = pure 0
hexDigit '1' = pure 1
hexDigit '2' = pure 2
hexDigit '3' = pure 3
hexDigit '4' = pure 4
hexDigit '5' = pure 5
hexDigit '6' = pure 6
hexDigit '7' = pure 7
hexDigit '8' = pure 8
hexDigit '9' = pure 9
hexDigit 'a' = pure 10
hexDigit 'A' = pure 10
hexDigit 'b' = pure 11
hexDigit 'B' = pure 11
hexDigit 'c' = pure 12
hexDigit 'C' = pure 12
hexDigit 'd' = pure 13
hexDigit 'D' = pure 13
hexDigit 'e' = pure 14
hexDigit 'E' = pure 14
hexDigit 'f' = pure 15
hexDigit 'F' = pure 15
hexDigit c   = Argo.raise (invalidHex c)


getExpr :: Expression -> CryptolCommand (Expr PName)
getExpr = CryptolCommand . const . getCryptolExpr

-- N.B., used in SAWServer as well, hence the more generic monad
getCryptolExpr :: (Argo.Method m, Monad m) => Expression -> m (Expr PName)
getCryptolExpr Unit =
  return $
    ETyped
      (ETuple [])
      (TTuple [])
getCryptolExpr (Bit b) =
  return $
    ETyped
      (EVar (UnQual (mkIdent $ if b then "True" else "False")))
      TBit
getCryptolExpr (Integer i) =
  return $
    ETyped
      (ELit (ECNum i (DecLit (pack (show i)))))
      (TUser (UnQual (mkIdent "Integer")) [])
getCryptolExpr (IntegerModulo i n) =
  return $
    ETyped
      (ELit (ECNum i (DecLit (pack (show i)))))
      (TUser (UnQual (mkIdent "Z")) [TNum n])
getCryptolExpr (Num enc txt w) =
  do d <- decode enc txt
     return $ ETyped
       (ELit (ECNum d (DecLit txt)))
       (TSeq (TNum w) TBit)
getCryptolExpr (Record fields) =
  fmap (ERecord . recordFromFields) $ for (HM.toList fields) $
  \(recName, spec) ->
    (mkIdent recName,) . (emptyRange,) <$> getCryptolExpr spec
getCryptolExpr (Sequence elts) =
  EList <$> traverse getCryptolExpr elts
getCryptolExpr (Tuple projs) =
  ETuple <$> traverse getCryptolExpr projs
getCryptolExpr (Concrete syntax) =
  case parseExpr syntax of
    Left err ->
      Argo.raise (cryptolParseErr syntax err)
    Right e -> pure e
getCryptolExpr (Let binds body) =
  EWhere <$> getCryptolExpr body <*> traverse mkBind binds
  where
    mkBind (LetBinding x rhs) =
      DBind .
      (\bindBody ->
         Bind { bName = fakeLoc (UnQual (mkIdent x))
              , bParams = []
              , bDef = bindBody
              , bSignature = Nothing
              , bInfix = False
              , bFixity = Nothing
              , bPragmas = []
              , bMono = True
              , bDoc = Nothing
              , bExport = Public
              }) .
      fakeLoc .
      DExpr <$>
        getCryptolExpr rhs

    fakeLoc = Located emptyRange
getCryptolExpr (Application fun (arg :| [])) =
  EApp <$> getCryptolExpr fun <*> getCryptolExpr arg
getCryptolExpr (Application fun (arg1 :| (arg : args))) =
  getCryptolExpr (Application (Application fun (arg1 :| [])) (arg :| args))
getCryptolExpr (TypeApplication gen (TypeArguments args)) =
  EAppT <$> getCryptolExpr gen <*> pure (map inst (Map.toList args))
  where
    inst (n, t) = NamedInst (Named (Located emptyRange n) (unJSONPType t))

-- TODO add tests that this is big-endian
-- | Interpret a ByteString as an Integer
bytesToInt :: BS.ByteString -> Integer
bytesToInt bs =
  BS.foldl' (\acc w -> (acc * 256) + toInteger w) 0 bs

readBack :: TValue -> Value -> Eval Expression
readBack ty val =
  case ty of
    -- TODO, add actual support for newtypes
    TVNewtype _u _ts _tfs -> liftIO $ throwIO (invalidType (tValTy ty))

    TVRec tfs ->
      Record . HM.fromList <$>
        sequence [ do fv <- evalSel C.Concrete val (RecordSel f Nothing)
                      fa <- readBack t fv
                      return (identText f, fa)
                 | (f, t) <- canonicalFields tfs
                 ]
    TVTuple [] ->
      pure Unit
    TVTuple ts ->
      Tuple <$> sequence [ do v <- evalSel C.Concrete val (TupleSel n Nothing)
                              a <- readBack t v
                              return a
                         | (n, t) <- zip [0..] ts
                         ]
    TVBit ->
      case val of
        VBit b -> pure (Bit b)
        _ -> mismatchPanic
    TVInteger ->
      case val of
        VInteger i -> pure (Integer i)
        _ -> mismatchPanic
    TVIntMod n ->
      case val of
        VInteger i -> pure (IntegerModulo i n)
        _ -> mismatchPanic
    TVSeq len contents
      | contents == TVBit
      , VWord width wv <- val ->
        do BV w v <- asWordVal C.Concrete wv
           let hexStr = T.pack $ showHex v ""
           let paddedLen = fromIntegral ((width `quot` 4) + (if width `rem` 4 == 0 then 0 else 1))
           return $ Num Hex (T.justifyRight paddedLen '0' hexStr) w
      | VSeq _l (enumerateSeqMap len -> vs) <- val ->
        Sequence <$> mapM (>>= readBack contents) vs

    other -> liftIO $ throwIO (invalidType (tValTy other))
  where
    mismatchPanic =
      error $ "Internal error: readBack: value '" <>
              show val <>
              "' didn't match type '" <>
              show (tValTy ty) <>
              "'"


observe :: Eval a -> CryptolCommand a
observe e = liftIO (runEval mempty e)

mkEApp :: Expr PName -> [Expr PName] -> Expr PName
mkEApp f args = foldl EApp f args

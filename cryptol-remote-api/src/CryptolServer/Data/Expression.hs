{-# OPTIONS_GHC -fno-warn-type-defaults #-}
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

import Cryptol.Eval (evalSel)
import Cryptol.Eval.Concrete (primTable, Value)
import Cryptol.Eval.Value (GenValue(..), asWordVal, enumerateSeqMap)
import Cryptol.Parser
import Cryptol.Parser.AST (Bind(..), BindDef(..), Decl(..), Expr(..), Type(..), PName(..), Literal(..), NumInfo(..))
import Cryptol.Parser.Position (Located(..), emptyRange)
import Cryptol.Parser.Selector
import Cryptol.TypeCheck.AST (PrimMap)
import Cryptol.TypeCheck.SimpType (tRebuild)
import qualified Cryptol.TypeCheck.Type as TC
import Cryptol.Utils.Ident
import Cryptol.Utils.RecordMap (recordFromFields, canonicalFields)


import Argo
import CryptolServer
import CryptolServer.Exceptions

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
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Ord, Show)

data ExpressionTag =
    TagNum | TagRecord | TagSequence | TagTuple | TagUnit | TagLet | TagApp | TagIntMod

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
  toJSON TagIntMod   = "integer modulo"

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


decode :: Encoding -> Text -> Method s Integer
decode Base64 txt =
  let bytes = encodeUtf8 txt
  in
    case Base64.decode bytes of
      Left err ->
        raise (invalidBase64 bytes err)
      Right decoded -> return $ bytesToInt decoded
decode Hex txt =
  squish <$> traverse hexDigit (T.unpack txt)
  where
    squish = foldl (\acc i -> (acc * 16) + i) 0

hexDigit :: Num a => Char -> Method s a
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
hexDigit c   = raise (invalidHex c)


getExpr :: Expression -> Method s (Expr PName)
getExpr Unit =
  return $
    ETyped
      (ETuple [])
      (TTuple [])
getExpr (Bit b) =
  return $
    ETyped
      (EVar (UnQual (mkIdent $ if b then "True" else "False")))
      TBit
getExpr (Integer i) =
  return $
    ETyped
      (ELit (ECNum i (DecLit (pack (show i)))))
      (TUser (UnQual (mkIdent "Integer")) [])
getExpr (IntegerModulo i n) =
  return $
    ETyped
      (ELit (ECNum i (DecLit (pack (show i)))))
      (TUser (UnQual (mkIdent "Z")) [TNum n])
getExpr (Num enc txt w) =
  do d <- decode enc txt
     return $ ETyped
       (ELit (ECNum d (DecLit txt)))
       (TSeq (TNum w) TBit)
getExpr (Record fields) =
  fmap (ERecord . recordFromFields) $ for (HM.toList fields) $
  \(recName, spec) ->
    (mkIdent recName,) . (emptyRange,) <$> getExpr spec
getExpr (Sequence elts) =
  EList <$> traverse getExpr elts
getExpr (Tuple projs) =
  ETuple <$> traverse getExpr projs
getExpr (Concrete syntax) =
  case parseExpr syntax of
    Left err ->
      raise (cryptolParseErr syntax err)
    Right e -> pure e
getExpr (Let binds body) =
  EWhere <$> getExpr body <*> traverse mkBind binds
  where
    mkBind (LetBinding x rhs) =
      DBind .
      (\bindBody ->
         Bind (fakeLoc (UnQual (mkIdent x))) [] bindBody Nothing False Nothing [] True Nothing) .
      fakeLoc .
      DExpr <$>
        getExpr rhs

    fakeLoc = Located emptyRange
getExpr (Application fun (arg :| [])) =
  EApp <$> getExpr fun <*> getExpr arg
getExpr (Application fun (arg1 :| (arg : args))) =
  getExpr (Application (Application fun (arg1 :| [])) (arg :| args))

-- TODO add tests that this is big-endian
-- | Interpret a ByteString as an Integer
bytesToInt :: BS.ByteString -> Integer
bytesToInt bs =
  BS.foldl' (\acc w -> (acc * 256) + toInteger w) 0 bs

typeNum :: (Alternative f, Integral a) => TC.Type -> f a
typeNum (tRebuild -> (TC.TCon (TC.TC (TC.TCNum n)) [])) =
  pure $ fromIntegral n
typeNum _ = empty

readBack :: PrimMap -> TC.Type -> Value -> Eval Expression
readBack prims ty val =
  let tbl = primTable theEvalOpts in
  let ?evalPrim = \i -> Right <$> Map.lookup i tbl in
  case TC.tNoUser ty of
    TC.TRec tfs ->
      Record . HM.fromList <$>
        sequence [ do fv <- evalSel C.Concrete val (RecordSel f Nothing)
                      fa <- readBack prims t fv
                      return (identText f, fa)
                 | (f, t) <- canonicalFields tfs
                 ]
    TC.TCon (TC.TC (TC.TCTuple _)) [] ->
      pure Unit
    TC.TCon (TC.TC (TC.TCTuple _)) ts ->
      Tuple <$> sequence [ do v <- evalSel C.Concrete val (TupleSel n Nothing)
                              a <- readBack prims t v
                              return a
                         | (n, t) <- zip [0..] ts
                         ]
    TC.TCon (TC.TC TC.TCBit) [] ->
      case val of
        VBit b -> pure (Bit b)
        _ -> mismatchPanic
    TC.TCon (TC.TC TC.TCInteger) [] ->
      case val of
        VInteger i -> pure (Integer i)
        _ -> mismatchPanic
    TC.TCon (TC.TC TC.TCIntMod) [typeNum -> Just n] ->
      case val of
        VInteger i -> pure (IntegerModulo i n)
        _ -> mismatchPanic
    TC.TCon (TC.TC TC.TCSeq) [TC.tNoUser -> len, TC.tNoUser -> contents]
      | len == TC.tZero ->
        return Unit
      | contents == TC.TCon (TC.TC TC.TCBit) []
      , VWord _ wv <- val ->
        do BV w v <- wv >>= asWordVal C.Concrete
           return $ Num Hex (T.pack $ showHex v "") w
      | TC.TCon (TC.TC (TC.TCNum k)) [] <- len
      , VSeq _l (enumerateSeqMap k -> vs) <- val ->
        Sequence <$> mapM (>>= readBack prims contents) vs
    other -> liftIO $ throwIO (invalidType other)
  where
    mismatchPanic =
      error $ "Internal error: readBack: value '" <>
              show val <>
              "' didn't match type '" <>
              show ty <>
              "'"


observe :: Eval a -> Method ServerState a
observe e = liftIO (runEval e)

mkEApp :: Expr PName -> [Expr PName] -> Expr PName
mkEApp f args = foldl EApp f args

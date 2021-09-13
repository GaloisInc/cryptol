{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module CryptolServer.ServiceCode
  where

import System.Random

import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.Aeson as JSON
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Bits
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as BS.Base64
import qualified Data.ByteArray as BA
import Data.Word8 (Word8)

import Control.Monad (void, (<=<))
import Control.Monad.IO.Class (MonadIO(..))

import Crypto.Cipher.Types (AuthTag(..), cipherInit)
import qualified Crypto.Cipher.AES as AES
import qualified Crypto.Cipher.AESGCMSIV as AESGCMSIV
import Crypto.Error (maybeCryptoError)

import Argo (makeJSONRPCException)
import qualified Argo.Doc as Doc

import qualified Cryptol.Eval.Env as E
import qualified Cryptol.Eval.Type as E
import Cryptol.ModuleSystem (evalExpr, checkExpr, loadModuleByName, deEnv, meDynEnv)
import Cryptol.Parser (parseModName)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import qualified Cryptol.TypeCheck.Type as CT
import qualified Cryptol.Parser.AST as P

import CryptolServer
import CryptolServer.Data.Expression
import CryptolServer.Exceptions

serviceCodeDescr :: Doc.Block
serviceCodeDescr =
  Doc.Paragraph
    [Doc.Text "Evaluate the result of calling a Cryptol function on randomized parameters."]

-- TODO
getEntropy :: MonadIO m => Integer -> m [Bool]
getEntropy w
  | w > 0 = (:) <$> liftIO randomIO <*> getEntropy (w - 1)
  | otherwise = pure []

-- TODO
encryptOutput :: MonadIO m => ByteString -> m (Maybe ByteString)
encryptOutput plaintext
  | Just cipher <- maybeCryptoError (cipherInit @AES.AES256 $ ("foobarbaz" :: ByteString))
  = do
      nonce <- liftIO AESGCMSIV.generateNonce
      let (tag, ct) = AESGCMSIV.encrypt cipher nonce BS.empty plaintext
      pure . Just $ BA.convert nonce <> BA.convert tag <> ct
  | otherwise = pure Nothing

decryptInput :: MonadIO m => ByteString -> m (Maybe ByteString)
decryptInput ciphertext
  | Just cipher <- maybeCryptoError (cipherInit @AES.AES256 $ ("foobarbaz" :: ByteString))
  , Just nonce <- maybeCryptoError . AESGCMSIV.nonce $ BA.take 12 ciphertext
  = do
      let tag = AuthTag . BA.convert . BA.take 16 $ BA.drop 12 ciphertext
      let ct = BA.drop 28 ciphertext
      pure $ AESGCMSIV.decrypt cipher nonce BS.empty ct tag
  | otherwise = pure Nothing

-- Given a (curried) function type, extract the given number of argument types
funTypeTake :: Int -> CT.Type -> [CT.Type]
funTypeTake n t
   | n > 0
   , Just (dom, cod) <- CT.tIsFun t
   = dom : funTypeTake (n - 1) cod
   | otherwise = []

-- Generate a random literal expression of the given (bitvector) type
randTermOfType :: CT.Type -> CryptolCommand (P.Expr P.PName)
randTermOfType t
  | Just (n, b) <- CT.tIsSeq t
  , CT.tIsBit b
  , Just w <- CT.tIsNum n = do
      entropy <- getEntropy w
      getExpr (Sequence $ Bit <$> entropy)
  | otherwise = raise $ makeJSONRPCException 20300 "Can't generate random term of argument type" (Nothing :: Maybe ())

byteStringToExpr :: ByteString -> CryptolCommand (P.Expr P.PName)
byteStringToExpr bs = getExpr (Sequence $ Bit <$> bits)
  where
    bits :: [Bool]
    bits = concatMap byteBits $ BS.unpack bs
    byteBits :: Word8 -> [Bool]
    byteBits = go 8 []
      where
        go :: Int -> [Bool] -> Word8 -> [Bool]
        go 0 acc _ = acc
        go n acc b = go (n - 1) ((b .&. 1 /= 0):acc) (shiftR b 1)

exprToByteString :: Expression -> CryptolCommand ByteString
exprToByteString expr
  | Sequence s <- expr
  , Just bits <- sequence $ (\case Bit b -> Just b; _ -> Nothing) <$> s
  , Just bytes <- bitsToBytes bits
  = pure $ BS.pack bytes
  | otherwise = raise $ makeJSONRPCException 20301 "Can't convert result to bytestring" (Nothing :: Maybe ())
  where
    wordOf :: Bool -> Word8
    wordOf True = 1
    wordOf False = 0
    bitsToBytes :: [Bool] -> Maybe [Word8]
    bitsToBytes (b7:b6:b5:b4:b3:b2:b1:b0:rest) =
      let byte =
            shiftL (wordOf b7) 7
            .|. shiftL (wordOf b6) 6
            .|. shiftL (wordOf b5) 5
            .|. shiftL (wordOf b4) 4
            .|. shiftL (wordOf b3) 3
            .|. shiftL (wordOf b2) 2
            .|. shiftL (wordOf b1) 1
            .|. wordOf b0
      in (byte:) <$> bitsToBytes rest
    bitsToBytes [] = Just []
    bitsToBytes _ = Nothing

evalExpression :: P.Expr P.PName -> CryptolCommand Expression
evalExpression e = do
  (_expr, ty, schema) <- liftModuleCmd (checkExpr e)
  s <- getTCSolver
  perhapsDef <- liftIO (defaultReplExpr s ty schema)
  case perhapsDef of
    Nothing ->
      raise (evalPolyErr schema)
    Just (tys, checked) -> do
      let su = listParamSubst tys
      let theType = apSubst su (CT.sType schema)
      tenv  <- E.envTypes . deEnv . meDynEnv <$> getModuleEnv
      let tval = E.evalValType tenv theType
      val <- liftModuleCmd (evalExpr checked)
      readBack tval val >>= \case
        Nothing -> raise $ invalidType theType
        Just expr -> pure expr

serviceCode :: ServiceCodeParams -> CryptolCommand JSON.Value
serviceCode scp = do
  resetTCSolver
  case parseModName . Text.unpack $ serviceCodeName scp of
    Nothing -> raise
      . makeJSONRPCException 20303 "Invalid service code name"
      . Just $ serviceCodeName scp
    Just mn -> void $ liftModuleCmd (loadModuleByName mn)
  fun <- getExpr (Variable "operation")
  (_expr, funty, funschema) <- liftModuleCmd (checkExpr fun)
  s <- getTCSolver
  liftIO (defaultReplExpr s funty funschema) >>= \case
    Nothing -> raise (evalPolyErr funschema)
    Just (funtys, _) -> do
      let funsu = listParamSubst funtys
      let funtype = apSubst funsu (CT.sType funschema)
      let randArgTypes = funTypeTake (serviceCodeRandomArgs scp) funtype
      randArgs <- traverse randTermOfType randArgTypes
      let fromBase64 str = case BS.Base64.decode $ encodeUtf8 str of
            Left _ -> raise $ makeJSONRPCException 20304 "Invalid service code argument" (Nothing :: Maybe ())
            Right bs -> pure bs
      fixedArgs <- traverse (byteStringToExpr <=< fromBase64) $ serviceCodeFixedArgs scp
      let appExpr = mkEApp fun $ randArgs <> fixedArgs
      bs <- exprToByteString =<< evalExpression appExpr
      encryptOutput bs >>= \case
        Nothing -> raise $ makeJSONRPCException 20305 "Failed to wrap result" (Nothing :: Maybe ())
        Just ebs -> pure $ JSON.object ["result" .= decodeUtf8 (BS.Base64.encode ebs)]

data ServiceCodeParams = ServiceCodeParams
  { serviceCodeName :: Text
  , serviceCodeRandomArgs :: Int
  , serviceCodeFixedArgs :: [Text]
  }

instance FromJSON ServiceCodeParams where
  parseJSON = withObject "params for \"service_code\"" $ \o -> do
    serviceCodeName <- o .: "name"
    serviceCodeRandomArgs <- o .: "random"
    serviceCodeFixedArgs <- o .: "arguments"
    pure ServiceCodeParams{..}

instance Doc.DescribedMethod ServiceCodeParams JSON.Value where
  parameterFieldDescription =
    [("name",
      Doc.Paragraph [Doc.Text "The name of the service code."])
    , ("random",
      Doc.Paragraph [Doc.Text "The number of random bitvector arguments."])
    , ("arguments",
      Doc.Paragraph [Doc.Text "The non-random arguments."])
    ]

  resultFieldDescription =
    [ ("result",
      Doc.Paragraph [ Doc.Text "The result of the service code (a bytestring)"])
    ]

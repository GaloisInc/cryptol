-- |
-- Module      :  Cryptol.ModuleSystem.Fingerprint
-- Copyright   :  (c) 2019 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.ModuleSystem.Fingerprint
  ( Fingerprint
  , fingerprint
  , fingerprintFile
  , fingerprintHexString
  ) where

import Control.DeepSeq          (NFData (rnf))
import Control.Exception        (try)
import Control.Monad            ((<$!>))
import Crypto.Hash.SHA256       (hash)
import Data.ByteString          (ByteString)
import Data.Char (intToDigit, digitToInt, isHexDigit)
import qualified Data.ByteString as B
import qualified Toml
import qualified Toml.Schema as Toml

newtype Fingerprint = Fingerprint ByteString
  deriving (Eq, Ord, Show, Read)

instance NFData Fingerprint where
  rnf (Fingerprint fp) = rnf fp

-- | Compute a fingerprint for a bytestring.
fingerprint :: ByteString -> Fingerprint
fingerprint = Fingerprint . hash

-- | Attempt to compute the fingerprint of the file at the given path.
-- Returns 'Left' in the case of an error.
fingerprintFile :: FilePath -> IO (Either IOError Fingerprint)
fingerprintFile path =
  do res <- try (B.readFile path)
     return $! fingerprint <$!> (res :: Either IOError ByteString)

fingerprintHexString :: Fingerprint -> String
fingerprintHexString (Fingerprint bs) = B.foldr hex "" bs
  where
  hex b cs = let (x,y) = divMod (fromIntegral b) 16
             in intToDigit x : intToDigit y : cs

fingerprintFromHexString :: String -> Maybe Fingerprint
fingerprintFromHexString str = Fingerprint . B.pack <$> go str
  where
    go [] = Just []
    go (x:y:z)
      | isHexDigit x
      , isHexDigit y
      = (fromIntegral (digitToInt x * 16 + digitToInt y):) <$> go z
    go _ = Nothing

instance Toml.ToValue Fingerprint where
  toValue = Toml.toValue . fingerprintHexString

instance Toml.FromValue Fingerprint where
  fromValue x =
   do str <- Toml.fromValue x
      case fingerprintFromHexString str of
        Nothing -> Toml.failAt (Toml.valueAnn x) "malformed fingerprint hex-string"
        Just fp -> pure fp

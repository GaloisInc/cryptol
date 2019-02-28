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
  ) where

import Control.DeepSeq          (NFData (rnf))
import Crypto.Hash.SHA1         (hash)
import Data.ByteString          (ByteString)
import System.IO.Error          (IOError)
import Control.Exception        (try)
import qualified Data.ByteString as B

newtype Fingerprint = Fingerprint ByteString
  deriving (Eq, Show)

instance NFData Fingerprint where
  rnf (Fingerprint fp) = rnf fp

-- | Compute a fingerprint for a bytestring.
fingerprint :: ByteString -> Fingerprint
fingerprint = Fingerprint . hash

-- | Attempt to compute the fingerprint of the file at the given path.
-- Returns 'Nothing' in the case of an error.
fingerprintFile :: FilePath -> IO (Maybe Fingerprint)
fingerprintFile path =
  do res <- try (B.readFile path)
     return $!
       case res :: Either IOError ByteString of
         Left{}  -> Nothing
         Right b -> Just $! fingerprint b

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
import Crypto.Hash.SHA1         (hash)
import Data.ByteString          (ByteString)
import Control.Exception        (try)
import qualified Data.ByteString as B
import qualified Data.Vector as Vector

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

fingerprintHexString :: Fingerprint -> String
fingerprintHexString (Fingerprint bs) = B.foldr hex "" bs
  where
  digits   = Vector.fromList "0123456789ABCDEF"
  digit x  = digits Vector.! fromIntegral x
  hex b cs = let (x,y) = divMod b 16
             in digit x : digit y : cs



module CryptolServer.Utils (BS(..)) where

import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.ByteString as BS
import Data.Word
import Data.Bits

import Data.Aeson

-- | A wrapper around bytestring, to get a specific JSON representation
newtype BS = BS BS.ByteString

instance ToJSON BS where
  toJSON (BS bs0) = toJSON (BS.foldr showByte "" bs0)

instance FromJSON BS where
  parseJSON =
    withText "Bytes" $
    \txt -> case parseByteString txt of
              Just yes -> pure (BS (BS.pack yes))
              Nothing -> fail ("Invalid bytes: " ++ Text.unpack txt)

parseByteString :: Text -> Maybe [Word8]
parseByteString cs
  | Text.null cs = pure []
  | otherwise =
    do
      (x,xs) <- Text.uncons cs
      d1     <- parseHexDigit x
      (y,ys) <- Text.uncons xs
      d2     <- parseHexDigit y
      rest   <- parseByteString ys
      let d = ((d1 `shiftL` 4) .|. d2)
      pure (d : rest)

parseHexDigit :: Char -> Maybe Word8
parseHexDigit x
  | '0' <= x && x <= '9' = pure (toEnum (fromEnum x - fromEnum '0'))
  | 'a' <= x && x <= 'f' = pure (10 + toEnum (fromEnum x - fromEnum 'a'))
  | otherwise = Nothing

showHexDigit :: Word8 -> Char
showHexDigit n
  | n < 10    = toEnum (fromEnum '0' + fromEnum n)
  | otherwise = toEnum (fromEnum 'a' + (fromEnum n - 10))

showByte :: Word8 -> ShowS
showByte b bs = showHexDigit (b `shiftR` 4) :
                showHexDigit (b .&. 0xF)    :
                bs


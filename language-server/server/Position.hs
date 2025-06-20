module Position where

import Language.LSP.Protocol.Types qualified as LSP
import Cryptol.Parser.Position


rangeToLSP :: Range -> (LSP.Uri, LSP.Range)
rangeToLSP Range { source, from, to } =
  ( LSP.filePathToUri source,
    LSP.mkRange (fromIntegral (line from - 1))
                (fromIntegral (colOffset from))
                (fromIntegral (line to - 1))
                (fromIntegral (colOffset to))
  )
module SyntaxHighlight (semanticTokens) where

import Data.Maybe(mapMaybe)
import Data.Map qualified as Map
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Control.Lens((^.))

import Language.LSP.Protocol.Lens qualified as LSP
import Language.LSP.Protocol.Types qualified as LSP

import Cryptol.Parser.Position qualified as Cry
import Cryptol.Parser.Lexer
import Monad
import Config

semanticTokens :: LSP.Uri -> Maybe LSP.Range -> M [LSP.SemanticTokenAbsolute]
semanticTokens uri mbRange =
  do
    done <- lexedFiles <$> getState
    toks <- case Map.lookup uri done of   
              Just ts -> pure ts
              Nothing ->
                do ts <- liftIO (lexFile uri)
                   update \_ s -> pure (s { lexedFiles = Map.insert uri ts (lexedFiles s) }, ts)
    case mbRange of
      Nothing -> pure toks
      Just r  ->
        let s  = r ^. LSP.start
            sl = s ^. LSP.line
            e  = r ^. LSP.end
            el = e ^. LSP.line
        in pure [ t | t <- toks,
                      let l = t ^. LSP.line,
                      sl <= l && l <= el -- only compare lines for simplicity
                    ]
  
    


-- | Lex the given file.
lexFile  :: LSP.Uri -> IO [LSP.SemanticTokenAbsolute]
lexFile uri =
  case LSP.uriToFilePath uri of
    Nothing -> pure []
    Just file ->
      do txt <- Text.readFile file
         let (ls,_) = primLexer defaultConfig txt
         pure (mapMaybe toAbsolute ls)

-- | Convert a Cryptol token to an LSP one
toAbsolute :: Located Token -> Maybe LSP.SemanticTokenAbsolute
toAbsolute ltok =
  do
    ty <- tokType (tokenType (thing ltok))
    let rng   = srcRange ltok
        start = Cry.from rng
        end   = Cry.to rng
    pure LSP.SemanticTokenAbsolute {
       _line = fromIntegral (Cry.line start - 1),
       _startChar = fromIntegral (Cry.colOffset start),
       _length = if Cry.line start == Cry.line end
                   then fromIntegral (Cry.colOffset end - Cry.colOffset start + 1)
                   else fromIntegral (Text.length (tokenText (thing ltok))),
       _tokenType = ty,
       _tokenModifiers = []
     }

-- | Classify tokens
tokType :: TokenT -> Maybe LSP.SemanticTokenTypes
tokType tok =
  case tok of
    Num {}      -> pure LSP.SemanticTokenTypes_Number
    Frac {}     -> pure LSP.SemanticTokenTypes_Number
    ChrLit {}   -> pure LSP.SemanticTokenTypes_String

    Ident [] "Integer" -> pure LSP.SemanticTokenTypes_Type
    Ident [] "Bit"     -> pure LSP.SemanticTokenTypes_Type
    Ident [] "Bool"    -> pure LSP.SemanticTokenTypes_Type
    Ident [] "Z"    -> pure LSP.SemanticTokenTypes_Type

    Ident {}   -> pure LSP.SemanticTokenTypes_Variable
    StrLit {}   -> pure LSP.SemanticTokenTypes_String
    Selector {} -> pure LSP.SemanticTokenTypes_Property
    KW kw ->
      case kw of
        KW_x    -> pure LSP.SemanticTokenTypes_Variable
        KW_inf  -> pure LSP.SemanticTokenTypes_Type
        KW_fin  -> pure LSP.SemanticTokenTypes_Type
        _       -> pure LSP.SemanticTokenTypes_Keyword
    Op  {}      -> pure LSP.SemanticTokenTypes_Operator
    Sym {}      -> pure LSP.SemanticTokenTypes_Decorator
    Virt {}     -> Nothing
    White w ->
      case w of
        Space -> Nothing
        _     -> pure LSP.SemanticTokenTypes_Comment
    Err {}      -> Nothing
    EOF {}      -> Nothing
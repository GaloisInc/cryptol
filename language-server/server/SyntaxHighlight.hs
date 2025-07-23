module SyntaxHighlight (newMonitor, semanticTokens) where

import Data.Maybe(mapMaybe,listToMaybe)
import Data.Char(isSpace)
import Data.Map qualified as Map
import Data.Text(Text)
import Data.Text qualified as Text
import Control.Lens((^.))
import Control.Monad(unless)
import Control.Concurrent(forkIO)
import Control.Monad.STM
import Control.Concurrent.STM.TVar

import Language.LSP.Server qualified as LSP
import Language.LSP.VFS qualified as LSP (virtualFileText)
import Language.LSP.Protocol.Lens qualified as LSP
import Language.LSP.Protocol.Types qualified as LSP

-- import Cryptol.Utils.PP
import Cryptol.Parser.Position qualified as Cry
import Cryptol.Parser.Lexer
import Monad
import State
import Position
import Index

newMonitor :: LSP.NormalizedUri -> M ()
newMonitor uri =
  do
    let timeout = 1000 -- Wait for no changes for 1s before updating
    changes <- liftIO (newTVarIO False)
    env     <- LSP.getLspEnv
    let loop =
          do
            atomically 
              do
                check =<< readTVar changes
                writeTVar changes False
            waitForPause timeout changes
            LSP.runLspT env (lexFile uri >> requestSemTokUpdate) 
            loop
    tid <- liftIO (forkIO loop)
    update_ \s -> s { cryRoots = Map.insert uri (tid, changes) (cryRoots s) }


waitForPause :: Int -> TVar Bool -> IO ()
waitForPause n changes =
  do
    itsTime <- registerDelay n
    ready <- atomically $
      do ch <- readTVar changes
         check ch
         writeTVar changes False
         pure False
      `orElse`
        do check =<< readTVar itsTime
           pure True
          
    unless ready (waitForPause n changes)

semanticTokens ::
  LSP.Uri ->
  Maybe LSP.Range ->
  M ([LSP.SemanticTokenAbsolute], [LSP.FoldingRange])
semanticTokens uri0 mbRange =
  do
    let uri = LSP.toNormalizedUri uri0
    done <- lexedFiles <$> getState
    (toks,fs) <-
      case Map.lookup uri done of   
        Just ts -> pure ts
        Nothing -> lexFile uri
    -- mapM_ (lspLog Info . Text.pack . show) toks
    case mbRange of
      Nothing -> pure (toks,fs)
      Just r  ->
        let s  = r ^. LSP.start
            sl = s ^. LSP.line
            e  = r ^. LSP.end
            el = e ^. LSP.line
        in pure ( [ t | t <- toks,
                      let l = t ^. LSP.line,
                      sl <= l && l <= el -- only compare lines for simplicity
                  ], fs )
  

-- | Lex the given file.
lexFile  :: LSP.NormalizedUri -> M ([LSP.SemanticTokenAbsolute], [LSP.FoldingRange])
lexFile uri =
  do
    mb <- LSP.getVirtualFile uri
    extra  <- lookupExtraSemToks uri . cryIndex <$> getState
    -- let non r = r { Cry.source = "" }
    -- lspLog Info ("Folds: " <+> hsep (map (pp . non) (extraFold extra)))
    -- lspLog Info (vcat (extraDbgMsgs extra))
    let 
        fs = map (mkFoldingRange LSP.FoldingRangeKind_Region Nothing) (extraFold extra)
        ts =
          case mb of
            Nothing -> ([],[])
            Just f ->
              let txt = LSP.virtualFileText f
                  (ls,_) = primLexer defaultConfig txt
              in (concatMap (toAbsolute (extraSemToks extra)) ls,
                  fs ++ mapMaybe tokenRange ls)
    update \_ s -> pure (s { lexedFiles = Map.insert uri ts (lexedFiles s) }, ts)
      

mkFoldingRange :: LSP.FoldingRangeKind -> Maybe Text -> Cry.Range -> LSP.FoldingRange
mkFoldingRange k txt rng =
  LSP.FoldingRange {
    _startLine = p1 ^. LSP.line,
    _startCharacter = Just (p1 ^. LSP.character),
    _endLine = p2 ^. LSP.line,
    _endCharacter = Just (p2 ^. LSP.character),
    _kind = Just k,
    _collapsedText = txt
  }
  where
  (_, r) = rangeToLSP rng
  p1 = r ^. LSP.start
  p2 = r ^. LSP.end


tokenRange :: Located Token -> Maybe LSP.FoldingRange
tokenRange ltok =
  case tokenType (thing ltok) of
    White DocStr -> Just folding
    White BlockComment -> Just folding
    _ -> Nothing
  where
  folding = mkFoldingRange LSP.FoldingRangeKind_Comment txt (srcRange ltok)
  boring = Text.all (\c -> isSpace c || c == '/' || c == '*')
  txt = listToMaybe 
      $ dropWhile boring
      $ Text.lines
      $ tokenText
      $ thing ltok    

-- | Convert a Cryptol token to an LSP one
toAbsolute ::
  (Cry.Range -> Maybe LSP.SemanticTokenTypes) ->
  Located Token ->
  [LSP.SemanticTokenAbsolute]
toAbsolute knownToks ltok =
  do
    let rng   = srcRange ltok
    ty <-
      case tokenType (thing ltok) of
        Ident {} | Just t <- knownToks rng -> pure t
        Num {} | Just t <- knownToks rng
               , t == LSP.SemanticTokenTypes_Type -> pure t
        _ -> tokType (tokenType (thing ltok))
    let start = Cry.from rng
        end   = Cry.to rng
        startL = fromIntegral (Cry.line start - 1)
        startC = fromIntegral (Cry.colOffset start)
        endC   = fromIntegral (Cry.colOffset end)
    if Cry.line start == Cry.line end
      then
        [ LSP.SemanticTokenAbsolute {
           _line = startL,
           _startChar = fromIntegral (Cry.colOffset start),
           _length = endC - startC,
           _tokenType = ty,
           _tokenModifiers = []
         } ]
      else loop ty startL startC endC (tokenText (thing ltok))

  where
  loop ty l startC endC txt =
    case Text.break (== '\n') txt of
      (as,bs)
        | Text.null bs -> [
          LSP.SemanticTokenAbsolute {
             _line = l,
             _startChar = startC,
             _length = endC - startC,
             _tokenType = ty,
             _tokenModifiers = []
           }
        ]
        | otherwise ->
          LSP.SemanticTokenAbsolute {
             _line = l,
             _startChar = startC,
             _length = fromIntegral (Text.length as),
             _tokenType = ty,
             _tokenModifiers = []
           } : loop ty (l+1) 0 endC (Text.drop 1 bs)
      
      

-- | Classify tokens
tokType :: TokenT -> [LSP.SemanticTokenTypes]
tokType tok =
  case tok of
    Num {}      -> pure LSP.SemanticTokenTypes_Number
    Frac {}     -> pure LSP.SemanticTokenTypes_Number
    ChrLit {}   -> pure LSP.SemanticTokenTypes_String
    Ident {}    -> pure LSP.SemanticTokenTypes_Variable
    StrLit {}   -> pure LSP.SemanticTokenTypes_String
    Selector {} -> pure LSP.SemanticTokenTypes_Property
    KW kw ->
      case kw of
        KW_x    -> pure LSP.SemanticTokenTypes_Variable
        KW_inf  -> pure LSP.SemanticTokenTypes_Type
        KW_fin  -> pure LSP.SemanticTokenTypes_Type
        _       -> pure LSP.SemanticTokenTypes_Keyword
    Op  {}      -> pure LSP.SemanticTokenTypes_Operator
    Sym {}      -> pure LSP.SemanticTokenTypes_Operator
    Virt {}     -> []
    White w ->
      case w of
        Space -> []
        _     -> pure LSP.SemanticTokenTypes_Comment
    Err {}      -> []
    EOF {}      -> []
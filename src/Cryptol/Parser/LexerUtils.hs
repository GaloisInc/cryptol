-- |
-- Module      :  Cryptol.Parser.LexerUtils
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Parser.LexerUtils where

import           Control.Monad(guard)
import           Data.Char(toLower,generalCategory,isAscii,ord,isSpace,
                                                            isAlphaNum,isAlpha)
import qualified Data.Char as Char
import           Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.Read as T
import           Data.Word(Word8)

import Cryptol.Utils.Panic
import Cryptol.Parser.Position
import Cryptol.Parser.Token
import Cryptol.Parser.Unlit(PreProc(None))



data Config = Config
  { cfgSource      :: !FilePath     -- ^ File that we are working on
  , cfgStart       :: !Position     -- ^ Starting position for the parser
  , cfgLayout      :: !Layout       -- ^ Settings for layout processing
  , cfgPreProc     :: PreProc       -- ^ Preprocessor settings
  , cfgAutoInclude :: [FilePath]    -- ^ Implicit includes
  , cfgModuleScope :: Bool          -- ^ When we do layout processing
                                    -- should we add a vCurly (i.e., are
                                    -- we parsing a list of things).
  }

defaultConfig :: Config
defaultConfig  = Config
  { cfgSource      = ""
  , cfgStart       = start
  , cfgLayout      = Layout
  , cfgPreProc     = None
  , cfgAutoInclude = []
  , cfgModuleScope = True
  }


type Action = Config -> Position -> Text -> LexS
           -> ([Located Token], LexS)

data LexS   = Normal
            | InComment Bool Position ![Position] [Text]
            | InString Position Text
            | InChar   Position Text


startComment :: Bool -> Action
startComment isDoc _ p txt s = ([], InComment d p stack chunks)
  where (d,stack,chunks) = case s of
                           Normal                -> (isDoc, [], [txt])
                           InComment doc q qs cs -> (doc, q : qs, txt : cs)
                           _                     -> panic "[Lexer] startComment" ["in a string"]

endComment :: Action
endComment cfg p txt s =
  case s of
    InComment d f [] cs     -> ([mkToken d f cs], Normal)
    InComment d _ (q:qs) cs -> ([], InComment d q qs (txt : cs))
    _                     -> panic "[Lexer] endComment" ["outside comment"]
  where
  mkToken isDoc f cs =
    let r   = Range { from = f, to = moves p txt, source = cfgSource cfg }
        str = T.concat $ reverse $ txt : cs

        tok = if isDoc then DocStr else BlockComment
    in Located { srcRange = r, thing = Token (White tok) str }

addToComment :: Action
addToComment _ _ txt s = ([], InComment doc p stack (txt : chunks))
  where
  (doc, p, stack, chunks) =
     case s of
       InComment d q qs cs -> (d,q,qs,cs)
       _                   -> panic "[Lexer] addToComment" ["outside comment"]

startEndComment :: Action
startEndComment cfg p txt s =
  case s of
    Normal -> ([tok], Normal)
      where tok = Located
                    { srcRange = Range { from   = p
                                       , to     = moves p txt
                                       , source = cfgSource cfg
                                       }
                    , thing = Token (White BlockComment) txt
                    }
    InComment d p1 ps cs -> ([], InComment d p1 ps (txt : cs))
    _ -> panic "[Lexer] startEndComment" ["in string or char?"]

startString :: Action
startString _ p txt _ = ([],InString p txt)

endString :: Action
endString cfg pe txt s = case s of
  InString ps str -> ([mkToken ps str], Normal)
  _               -> panic "[Lexer] endString" ["outside string"]
  where
  parseStr s1 = case reads s1 of
                  [(cs, "")] -> StrLit cs
                  _          -> Err InvalidString

  mkToken ps str = Located { srcRange = Range
                               { from   = ps
                               , to     = moves pe txt
                               , source = cfgSource cfg
                               }
                           , thing    = Token
                               { tokenType = parseStr (T.unpack tokStr)
                               , tokenText = tokStr
                               }
                           }
    where
    tokStr = str `T.append` txt


addToString :: Action
addToString _ _ txt s = case s of
  InString p str -> ([],InString p (str `T.append` txt))
  _              -> panic "[Lexer] addToString" ["outside string"]


startChar :: Action
startChar _ p txt _   = ([],InChar p txt)

endChar :: Action
endChar cfg pe txt s =
  case s of
    InChar ps str -> ([mkToken ps str], Normal)
    _             -> panic "[Lexer] endString" ["outside character"]

  where
  parseChar s1 = case reads s1 of
                   [(cs, "")] -> ChrLit cs
                   _          -> Err InvalidChar

  mkToken ps str = Located { srcRange = Range
                               { from   = ps
                               , to     = moves pe txt
                               , source = cfgSource cfg
                               }
                           , thing    = Token
                               { tokenType = parseChar (T.unpack tokStr)
                               , tokenText = tokStr
                               }
                           }
    where
    tokStr = str `T.append` txt



addToChar :: Action
addToChar _ _ txt s = case s of
  InChar p str -> ([],InChar p (str `T.append` txt))
  _              -> panic "[Lexer] addToChar" ["outside character"]


mkIdent :: Action
mkIdent cfg p s z = ([Located { srcRange = r, thing = Token t s }], z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Ident [] s

mkQualIdent :: Action
mkQualIdent cfg p s z = ([Located { srcRange = r, thing = Token t s}], z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Ident ns i
  (ns,i) = splitQual s

mkQualOp :: Action
mkQualOp cfg p s z = ([Located { srcRange = r, thing = Token t s}], z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Op (Other ns i)
  (ns,i) = splitQual s

emit :: TokenT -> Action
emit t cfg p s z  = ([Located { srcRange = r, thing = Token t s }], z)
  where r = Range { from = p, to = moves p s, source = cfgSource cfg }

emitS :: (Text -> TokenT) -> Action
emitS t cfg p s z  = emit (t s) cfg p s z

emitFancy :: (FilePath -> Position -> Text -> [Located Token]) -> Action
emitFancy f = \cfg p s z -> (f (cfgSource cfg) p s, z)


-- | Split out the prefix and name part of an identifier/operator.
splitQual :: T.Text -> ([T.Text], T.Text)
splitQual t =
  case splitNS (T.filter (not . isSpace) t) of
    []  -> panic "[Lexer] mkQualIdent" ["invalid qualified name", show t]
    [i] -> ([], i)
    xs  -> (init xs, last xs)

  where

  -- split on the namespace separator, `::`
  splitNS s =
    case T.breakOn "::" s of
      (l,r) | T.null r  -> [l]
            | otherwise -> l : splitNS (T.drop 2 r)



--------------------------------------------------------------------------------
numToken :: Text -> TokenT
numToken ds = case toVal of
                Just v  -> Num v rad (T.length ds')
                Nothing -> Err MalformedLiteral
  where
  rad
    | "0b" `T.isPrefixOf` ds = 2
    | "0o" `T.isPrefixOf` ds = 8
    | "0x" `T.isPrefixOf` ds = 16
    | otherwise              = 10

  ds1   = if rad == 10 then ds else T.drop 2 ds

  ds'   = T.filter (/= '_') ds1
  toVal = T.foldl' step (Just 0) ds'
  irad  = toInteger rad
  step mb x = do soFar <- mb
                 d     <- fromDigit irad x
                 pure $! (irad * soFar + d)

fromDigit :: Integer -> Char -> Maybe Integer
fromDigit r x' =
  do d <- v
     guard (d < r)
     pure d
  where
  x = toLower x'
  v | '0' <= x && x <= '9' = Just $ toInteger $      fromEnum x - fromEnum '0'
    | 'a' <= x && x <= 'z' = Just $ toInteger $ 10 + fromEnum x - fromEnum 'a'
    | otherwise            = Nothing


-- | Interpret something either as a fractional token,
-- a number followed by a selector, or an error.
fnumTokens :: FilePath -> Position -> Text -> [Located Token]
fnumTokens file pos ds =
  case wholeNum of
    Nothing -> [ tokFrom pos ds (Err MalformedLiteral) ]
    Just i
      | Just f <- fracNum, Just e <- expNum ->
        [ tokFrom pos ds (Frac ((fromInteger i + f) * (eBase ^^ e)) rad) ]
      | otherwise ->
        [ tokFrom pos        whole (Num i rad (T.length whole))
        , tokFrom afterWhole rest  (selectorToken rest)
        ]

  where
  tokFrom tpos txt t =
    Located { srcRange =
                 Range { from = tpos, to = moves tpos txt, source = file }
            , thing = Token { tokenText = txt, tokenType = t }
            }

  afterWhole = moves pos whole

  rad
    | "0b" `T.isPrefixOf` ds = 2
    | "0o" `T.isPrefixOf` ds = 8
    | "0x" `T.isPrefixOf` ds = 16
    | otherwise              = 10

  radI           = fromIntegral rad :: Integer
  radR           = fromIntegral rad :: Rational

  (whole,rest)   = T.break (== '.') (if rad == 10 then ds else T.drop 2 ds)
  digits         = T.filter (/= '_')
  expSym e       = if rad == 10 then toLower e == 'e' else toLower e == 'p'
  (frac,mbExp)   = T.break expSym (T.drop 1 rest)

  wholeStep mb c = do soFar <- mb
                      d     <- fromDigit radI c
                      pure $! (radI * soFar + d)

  wholeNum       = T.foldl' wholeStep (Just 0) (digits whole)

  fracStep mb c  = do soFar <- mb
                      d     <- fromInteger <$> fromDigit radI c
                      pure $! ((soFar + d) / radR)

  fracNum        = do let fds = T.reverse (digits frac)
                      guard (T.length fds > 0)
                      T.foldl' fracStep (Just 0) fds

  expNum         = case T.uncons mbExp of
                     Nothing -> Just (0 :: Integer)
                     Just (_,es) ->
                       case T.uncons es of
                         Just ('+', more) -> readDecimal more
                         Just ('-', more) -> negate <$> readDecimal more
                         _                -> readDecimal es

  eBase          = if rad == 10 then 10 else 2 :: Rational


-- assumes we start with a dot
selectorToken :: Text -> TokenT
selectorToken txt
  | Just n <- readDecimal body, n >= 0 = Selector (TupleSelectorTok n)
  | Just (x,xs) <- T.uncons body
  , id_first x
  , T.all id_next xs = Selector (RecordSelectorTok body)
  | otherwise = Err MalformedSelector

  where
  body = T.drop 1 txt
  id_first x = isAlpha x || x == '_'
  id_next  x = isAlphaNum x || x == '_' || x == '\''


readDecimal :: Integral a => Text -> Maybe a
readDecimal txt = case T.decimal txt of
                    Right (a,more) | T.null more -> Just a
                    _ -> Nothing


-------------------------------------------------------------------------------

data AlexInput            = Inp { alexPos           :: !Position
                                , alexInputPrevChar :: !Char
                                , input             :: !Text
                                } deriving Show

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte i =
  do (c,rest) <- T.uncons (input i)
     let i' = i { alexPos = move (alexPos i) c, input = rest }
         b  = byteForChar c
     pure (b, i')

data Layout = Layout | NoLayout


--------------------------------------------------------------------------------

-- | Drop white-space tokens from the input.
dropWhite :: [Located Token] -> [Located Token]
dropWhite = filter (notWhite . tokenType . thing)
  where notWhite (White w) = w == DocStr
        notWhite _         = True



-- | Collapse characters into a single Word8, identifying ASCII, and classes of
-- unicode.  This came from:
--
-- https://github.com/glguy/config-value/blob/master/src/Config/LexerUtils.hs
--
-- Which adapted:
--
-- https://github.com/ghc/ghc/blob/master/compiler/parser/Lexer.x
byteForChar :: Char -> Word8
byteForChar c
  | c <= '\6' = non_graphic
  | isAscii c = fromIntegral (ord c)
  | otherwise = case generalCategory c of
                  Char.LowercaseLetter       -> lower
                  Char.OtherLetter           -> lower
                  Char.UppercaseLetter       -> upper
                  Char.TitlecaseLetter       -> upper
                  Char.DecimalNumber         -> digit
                  Char.OtherNumber           -> digit
                  Char.ConnectorPunctuation  -> symbol
                  Char.DashPunctuation       -> symbol
                  Char.OtherPunctuation      -> symbol
                  Char.MathSymbol            -> symbol
                  Char.CurrencySymbol        -> symbol
                  Char.ModifierSymbol        -> symbol
                  Char.OtherSymbol           -> symbol
                  Char.Space                 -> sp
                  Char.ModifierLetter        -> other
                  Char.NonSpacingMark        -> other
                  Char.SpacingCombiningMark  -> other
                  Char.EnclosingMark         -> other
                  Char.LetterNumber          -> other
                  Char.OpenPunctuation       -> other
                  Char.ClosePunctuation      -> other
                  Char.InitialQuote          -> other
                  Char.FinalQuote            -> tick
                  _                          -> non_graphic
  where
  non_graphic     = 0
  upper           = 1
  lower           = 2
  digit           = 3
  symbol          = 4
  sp              = 5
  other           = 6
  tick            = 7

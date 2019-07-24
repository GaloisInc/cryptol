-- |
-- Module      :  Cryptol.Parser.LexerUtils
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
module Cryptol.Parser.LexerUtils where

import Cryptol.Parser.Position
import Cryptol.Parser.Unlit(PreProc(None))
import Cryptol.Utils.PP
import Cryptol.Utils.Panic

import           Data.Char(toLower,generalCategory,isAscii,ord,isSpace)
import qualified Data.Char as Char
import           Data.Text(Text)
import qualified Data.Text as T
import           Data.Word(Word8)

import GHC.Generics (Generic)
import Control.DeepSeq

data Config = Config
  { cfgSource      :: !FilePath     -- ^ File that we are working on
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
  , cfgLayout      = Layout
  , cfgPreProc     = None
  , cfgAutoInclude = []
  , cfgModuleScope = True
  }


type Action = Config -> Position -> Text -> LexS
           -> (Maybe (Located Token), LexS)

data LexS   = Normal
            | InComment Bool Position ![Position] [Text]
            | InString Position Text
            | InChar   Position Text


startComment :: Bool -> Action
startComment isDoc _ p txt s = (Nothing, InComment d p stack chunks)
  where (d,stack,chunks) = case s of
                           Normal                -> (isDoc, [], [txt])
                           InComment doc q qs cs -> (doc, q : qs, txt : cs)
                           _                     -> panic "[Lexer] startComment" ["in a string"]

endComment :: Action
endComment cfg p txt s =
  case s of
    InComment d f [] cs     -> (Just (mkToken d f cs), Normal)
    InComment d _ (q:qs) cs -> (Nothing, InComment d q qs (txt : cs))
    _                     -> panic "[Lexer] endComment" ["outside comment"]
  where
  mkToken isDoc f cs =
    let r   = Range { from = f, to = moves p txt, source = cfgSource cfg }
        str = T.concat $ reverse $ txt : cs

        tok = if isDoc then DocStr else BlockComment
    in Located { srcRange = r, thing = Token (White tok) str }

addToComment :: Action
addToComment _ _ txt s = (Nothing, InComment doc p stack (txt : chunks))
  where
  (doc, p, stack, chunks) =
     case s of
       InComment d q qs cs -> (d,q,qs,cs)
       _                   -> panic "[Lexer] addToComment" ["outside comment"]

startEndComment :: Action
startEndComment cfg p txt s =
  case s of
    Normal -> (Just tok, Normal)
      where tok = Located
                    { srcRange = Range { from   = p
                                       , to     = moves p txt
                                       , source = cfgSource cfg
                                       }
                    , thing = Token (White BlockComment) txt
                    }
    InComment d p1 ps cs -> (Nothing, InComment d p1 ps (txt : cs))
    _ -> panic "[Lexer] startEndComment" ["in string or char?"]

startString :: Action
startString _ p txt _ = (Nothing,InString p txt)

endString :: Action
endString cfg pe txt s = case s of
  InString ps str -> (Just (mkToken ps str), Normal)
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
  InString p str -> (Nothing,InString p (str `T.append` txt))
  _              -> panic "[Lexer] addToString" ["outside string"]


startChar :: Action
startChar _ p txt _   = (Nothing,InChar p txt)

endChar :: Action
endChar cfg pe txt s =
  case s of
    InChar ps str -> (Just (mkToken ps str), Normal)
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
  InChar p str -> (Nothing,InChar p (str `T.append` txt))
  _              -> panic "[Lexer] addToChar" ["outside character"]


mkIdent :: Action
mkIdent cfg p s z = (Just Located { srcRange = r, thing = Token t s }, z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Ident [] s

mkQualIdent :: Action
mkQualIdent cfg p s z = (Just Located { srcRange = r, thing = Token t s}, z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Ident ns i
  (ns,i) = splitQual s

mkQualOp :: Action
mkQualOp cfg p s z = (Just Located { srcRange = r, thing = Token t s}, z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Op (Other ns i)
  (ns,i) = splitQual s

emit :: TokenT -> Action
emit t cfg p s z  = (Just Located { srcRange = r, thing = Token t s }, z)
  where r = Range { from = p, to = moves p s, source = cfgSource cfg }


emitS :: (Text -> TokenT) -> Action
emitS t cfg p s z  = emit (t s) cfg p s z


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
numToken :: Integer -> Text -> TokenT
numToken rad ds = Num (toVal ds') (fromInteger rad) (T.length ds')
  where
  ds' = T.filter (/= '_') ds
  toVal = T.foldl' (\x c -> rad * x + fromDigit c) 0

fromDigit :: Char -> Integer
fromDigit x'
  | 'a' <= x && x <= 'z'  = toInteger (10 + fromEnum x - fromEnum 'a')
  | otherwise             = toInteger (fromEnum x - fromEnum '0')
  where x                 = toLower x'

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
     return (b,i')

data Layout = Layout | NoLayout


--------------------------------------------------------------------------------

-- | Drop white-space tokens from the input.
dropWhite :: [Located Token] -> [Located Token]
dropWhite = filter (notWhite . tokenType . thing)
  where notWhite (White w) = w == DocStr
        notWhite _         = True


data Block = Virtual Int     -- ^ Virtual layout block
           | Explicit TokenT -- ^ An explicit layout block, expecting this ending
                             -- token.
             deriving (Show)

isExplicit :: Block -> Bool
isExplicit Explicit{} = True
isExplicit Virtual{}  = False

startsLayout :: TokenT -> Bool
startsLayout (KW KW_where)    = True
startsLayout (KW KW_private)  = True
startsLayout (KW KW_parameter) = True
startsLayout _                = False

-- Add separators computed from layout
layout :: Config -> [Located Token] -> [Located Token]
layout cfg ts0 = loop False implicitScope [] ts0
  where

  (_pos0,implicitScope) = case ts0 of
    t : _ -> (from (srcRange t), cfgModuleScope cfg && tokenType (thing t) /= KW KW_module)
    _     -> (start,False)


  loop :: Bool -> Bool -> [Block] -> [Located Token] -> [Located Token]
  loop afterDoc startBlock stack (t : ts)
    | startsLayout ty    = toks ++ loop False True                             stack'  ts

    -- We don't do layout within these delimeters
    | Sym ParenL   <- ty = toks ++ loop False False (Explicit (Sym ParenR)   : stack') ts
    | Sym CurlyL   <- ty = toks ++ loop False False (Explicit (Sym CurlyR)   : stack') ts
    | Sym BracketL <- ty = toks ++ loop False False (Explicit (Sym BracketR) : stack') ts

    | EOF          <- ty = toks
    | White DocStr <- ty = toks ++ loop True  False                            stack'  ts
    | otherwise          = toks ++ loop False False                            stack'  ts

    where
    ty  = tokenType (thing t)
    pos = srcRange t

    (toks,offStack)
      | afterDoc  = ([t], stack)
      | otherwise = offsides startToks t stack

    -- add any block start tokens, and push a level on the stack
    (startToks,stack')
      | startBlock && ty == EOF = ( [ virt cfg (to pos) VCurlyR
                                    , virt cfg (to pos) VCurlyL ]
                                  , offStack )
      | startBlock = ( [ virt cfg (to pos) VCurlyL ], Virtual (col (from pos)) : offStack )
      | otherwise  = ( [], offStack )

  loop _ _ _ [] = panic "[Lexer] layout" ["Missing EOF token"]


  offsides :: [Located Token] -> Located Token -> [Block] -> ([Located Token], [Block])
  offsides startToks t = go startToks
    where
    go virts stack = case stack of

      -- delimit or close a layout block
      Virtual c : rest
          -- commas only close to an explicit marker, so if there is none, the
          -- comma doesn't close anything
        | Sym Comma == ty     ->
                         if any isExplicit rest
                            then go   (virt cfg (to pos) VCurlyR : virts) rest
                            else done                              virts  stack

        | closingToken        -> go   (virt cfg (to pos) VCurlyR : virts) rest
        | col (from pos) == c -> done (virt cfg (to pos) VSemi   : virts) stack
        | col (from pos) <  c -> go   (virt cfg (to pos) VCurlyR : virts) rest

      -- close an explicit block
      Explicit close : rest | close     == ty -> done virts rest
                            | Sym Comma == ty -> done virts stack

      _ -> done virts stack

    ty  = tokenType (thing t)
    pos = srcRange t

    done ts s = (reverse (t:ts), s)

    closingToken = ty `elem` [ Sym ParenR, Sym BracketR, Sym CurlyR ]

virt :: Config -> Position -> TokenV -> Located Token
virt cfg pos x = Located { srcRange = Range
                             { from = pos
                             , to = pos
                             , source = cfgSource cfg
                             }
                         , thing = t }
  where t = Token (Virt x) $ case x of
                               VCurlyL -> "beginning of layout block"
                               VCurlyR -> "end of layout block"
                               VSemi   -> "layout block separator"

--------------------------------------------------------------------------------

data Token    = Token { tokenType :: !TokenT, tokenText :: !Text }
                deriving (Show, Generic, NFData)

-- | Virtual tokens, inserted by layout processing.
data TokenV   = VCurlyL| VCurlyR | VSemi
                deriving (Eq, Show, Generic, NFData)

data TokenW   = BlockComment | LineComment | Space | DocStr
                deriving (Eq, Show, Generic, NFData)

data TokenKW  = KW_else
              | KW_extern
              | KW_fin
              | KW_if
              | KW_private
              | KW_include
              | KW_inf
              | KW_lg2
              | KW_lengthFromThen
              | KW_lengthFromThenTo
              | KW_max
              | KW_min
              | KW_module
              | KW_newtype
              | KW_pragma
              | KW_property
              | KW_then
              | KW_type
              | KW_where
              | KW_let
              | KW_x
              | KW_import
              | KW_as
              | KW_hiding
              | KW_infixl
              | KW_infixr
              | KW_infix
              | KW_primitive
              | KW_parameter
              | KW_constraint
              | KW_Prop
                deriving (Eq, Show, Generic, NFData)

-- | The named operators are a special case for parsing types, and 'Other' is
-- used for all other cases that lexed as an operator.
data TokenOp  = Plus | Minus | Mul | Div | Exp | Mod
              | Equal | LEQ | GEQ
              | Complement | Hash | At
              | Other [T.Text] T.Text
                deriving (Eq, Show, Generic, NFData)

data TokenSym = Bar
              | ArrL | ArrR | FatArrR
              | Lambda
              | EqDef
              | Comma
              | Semi
              | Dot
              | DotDot
              | DotDotDot
              | Colon
              | BackTick
              | ParenL   | ParenR
              | BracketL | BracketR
              | CurlyL   | CurlyR
              | TriL     | TriR
              | Underscore
                deriving (Eq, Show, Generic, NFData)

data TokenErr = UnterminatedComment
              | UnterminatedString
              | UnterminatedChar
              | InvalidString
              | InvalidChar
              | LexicalError
                deriving (Eq, Show, Generic, NFData)

data TokenT   = Num !Integer !Int !Int   -- ^ value, base, number of digits
              | ChrLit  !Char         -- ^ character literal
              | Ident ![T.Text] !T.Text -- ^ (qualified) identifier
              | StrLit !String         -- ^ string literal
              | KW    !TokenKW         -- ^ keyword
              | Op    !TokenOp         -- ^ operator
              | Sym   !TokenSym        -- ^ symbol
              | Virt  !TokenV          -- ^ virtual token (for layout)
              | White !TokenW          -- ^ white space token
              | Err   !TokenErr        -- ^ error token
              | EOF
                deriving (Eq, Show, Generic, NFData)

instance PP Token where
  ppPrec _ (Token _ s) = text (T.unpack s)

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

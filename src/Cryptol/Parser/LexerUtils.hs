-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
module Cryptol.Parser.LexerUtils where

import Cryptol.Parser.Position
import Cryptol.Parser.Unlit(PreProc(None))
import Cryptol.Utils.PP
import Cryptol.Utils.Panic

import Data.Char(toLower)
import Data.List(foldl')
import Data.Word(Word8)
import Codec.Binary.UTF8.String(encodeChar)


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


type Action = Config -> Position -> String -> LexS
           -> (Maybe (Located Token), LexS)

data LexS   = Normal
            | InComment Position ![Position] [String]
            | InString Position String
            | InChar   Position String


startComment :: Action
startComment _ p txt s = (Nothing, InComment p stack chunks)
  where (stack,chunks) = case s of
                           Normal            -> ([], [txt])
                           InComment q qs cs -> (q : qs, txt : cs)
                           _                 -> panic "[Lexer] startComment" ["in a string"]

endComent :: Action
endComent cfg p txt s =
  case s of
    InComment f [] cs     -> (Just (mkToken f cs), Normal)
    InComment _ (q:qs) cs -> (Nothing, InComment q qs (txt : cs))
    _                     -> panic "[Lexer] endComment" ["outside commend"]
  where
  mkToken f cs =
    let r   = Range { from = f, to = moves p txt, source = cfgSource cfg }
        str = concat $ reverse $ txt : cs
    in Located { srcRange = r, thing = Token (White BlockComment) str }

addToComment :: Action
addToComment _ _ txt s = (Nothing, InComment p stack (txt : chunks))
  where
  (p, stack, chunks) =
     case s of
       InComment q qs cs -> (q,qs,cs)
       _                 -> panic "[Lexer] addToComment" ["outside comment"]

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
                               { tokenType = parseStr (str ++ txt)
                               , tokenText = str ++ txt
                               }
                           }

addToString :: Action
addToString _ _ txt s = case s of
  InString p str -> (Nothing,InString p (str ++ txt))
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
                               { tokenType = parseChar (str ++ txt)
                               , tokenText = str ++ txt
                               }
                           }



addToChar :: Action
addToChar _ _ txt s = case s of
  InChar p str -> (Nothing,InChar p (str ++ txt))
  _              -> panic "[Lexer] addToChar" ["outside character"]


mkIdent :: Action
mkIdent cfg p s z = (Just Located { srcRange = r, thing = Token t s }, z)
  where
  r = Range { from = p, to = moves p s, source = cfgSource cfg }
  t = Ident s

emit :: TokenT -> Action
emit t cfg p s z  = (Just Located { srcRange = r, thing = Token t s }, z)
  where r = Range { from = p, to = moves p s, source = cfgSource cfg }


emitS :: (String -> TokenT) -> Action
emitS t cfg p s z  = emit (t s) cfg p s z



--------------------------------------------------------------------------------
numToken :: Integer -> String -> TokenT
numToken rad ds = Num (toVal ds) (fromInteger rad) (length ds)
  where
  toVal = foldl' (\x c -> rad * x + toDig c) 0
  toDig = if rad == 16 then fromHexDigit else fromDecDigit

fromDecDigit   :: Char -> Integer
fromDecDigit x  = read [x]

fromHexDigit :: Char -> Integer
fromHexDigit x'
  | 'a' <= x && x <= 'f'  = fromIntegral (10 + fromEnum x - fromEnum 'a')
  | otherwise             = fromDecDigit x
  where x                 = toLower x'



-------------------------------------------------------------------------------

data AlexInput            = Inp { alexPos           :: !Position
                                , alexInputPrevChar :: !Char
                                , input             :: !String
                                , moreBytes         :: ![Word8]
                                } deriving Show

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte i =
  case moreBytes i of
    b : bs -> Just (b, i { moreBytes = bs })
    [] ->
      case input i of
        c:cs -> alexGetByte Inp { alexPos = move (alexPos i) c
                                , alexInputPrevChar = c
                                , input             = cs
                                , moreBytes         = encodeChar c
                                }
        []   -> Nothing

data Layout = Layout | NoLayout


--------------------------------------------------------------------------------

-- | Drop white-space tokens from the input.
dropWhite :: [Located Token] -> [Located Token]
dropWhite = filter (notWhite . tokenType . thing)
  where notWhite (White _) = False
        notWhite _         = True


data Block = Virtual Int     -- ^ Virtual layout block
           | Explicit TokenT -- ^ An explicit layout block, expecting this ending
                             -- token.
             deriving (Show)

isExplicit :: Block -> Bool
isExplicit Explicit{} = True
isExplicit Virtual{}  = False

startsLayout :: TokenT -> Bool
startsLayout (KW KW_where)   = True
startsLayout (KW KW_private) = True
startsLayout _               = False

-- Add separators computed from layout
layout :: Config -> [Located Token] -> [Located Token]
layout cfg ts0 = loop implicitScope [] ts0
  where

  (_pos0,implicitScope) = case ts0 of
    t : _ -> (from (srcRange t), cfgModuleScope cfg && tokenType (thing t) /= KW KW_module)
    _     -> (start,False)


  loop :: Bool -> [Block] -> [Located Token] -> [Located Token]
  loop startBlock stack (t : ts)
    | startsLayout ty    = toks ++ loop True                             stack'  ts
    | Sym ParenL   <- ty = toks ++ loop False (Explicit (Sym ParenR)   : stack') ts
    | Sym CurlyL   <- ty = toks ++ loop False (Explicit (Sym CurlyR)   : stack') ts
    | Sym BracketL <- ty = toks ++ loop False (Explicit (Sym BracketR) : stack') ts
    | EOF          <- ty = toks
    | otherwise          = toks ++ loop False                            stack'  ts

    where
    ty  = tokenType (thing t)
    pos = srcRange t

    (toks,offStack) = offsides startToks t stack

    -- add any block start tokens, and push a level on the stack
    (startToks,stack')
      | startBlock && ty == EOF = ( [ virt cfg (to pos) VCurlyR
                                    , virt cfg (to pos) VCurlyL ]
                                  , offStack )
      | startBlock = ( [ virt cfg (to pos) VCurlyL ], Virtual (col (from pos)) : offStack )
      | otherwise  = ( [], offStack )

  loop _ _ [] = panic "[Lexer] layout" ["Missing EOF token"]


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

data Token    = Token { tokenType :: TokenT, tokenText :: String }
                deriving Show

-- | Virtual tokens, inserted by layout processing.
data TokenV   = VCurlyL| VCurlyR | VSemi
                deriving (Eq,Show)

data TokenW   = BlockComment | LineComment | Space
                deriving (Eq,Show)

data TokenKW  = KW_Arith
              | KW_Bit
              | KW_Cmp
              | KW_False
              | KW_True
              | KW_else
              | KW_Eq
              | KW_error
              | KW_extern
              | KW_fin
              | KW_if
              | KW_private
              | KW_include
              | KW_inf
              | KW_join
              | KW_lg2
              | KW_lengthFromThen
              | KW_lengthFromThenTo
              | KW_max
              | KW_min
              | KW_module
              | KW_newtype
              | KW_pragma
              | KW_pmult
              | KW_pdiv
              | KW_pmod
              | KW_property
              | KW_random
              | KW_reverse
              | KW_split
              | KW_splitAt
              | KW_then
              | KW_transpose
              | KW_type
              | KW_where
              | KW_let
              | KW_x
              | KW_zero
              | KW_import
              | KW_as
              | KW_hiding
                deriving (Eq,Show)

data TokenOp  = Plus | Minus | Mul | Div | Exp | Mod
              | NotEqual | Equal | LessThan | GreaterThan | LEQ | GEQ
              | EqualFun | NotEqualFun
              | ShiftL | ShiftR | RotL | RotR
              | Conj | Disj | Xor
              | Complement
              | Bang | BangBang | At | AtAt | Hash
                deriving (Eq,Show)

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
              | ColonColon
              | BackTick
              | ParenL   | ParenR
              | BracketL | BracketR
              | CurlyL   | CurlyR
              | TriL     | TriR
              | Underscore
                deriving (Eq,Show)

data TokenErr = UnterminatedComment
              | UnterminatedString
              | UnterminatedChar
              | InvalidString
              | InvalidChar
              | LexicalError
                deriving (Eq,Show)

data TokenT   = Num Integer Int Int   -- ^ value, base, number of digits
              | ChrLit  Char          -- ^ character literal
              | Ident String          -- ^ identifier
              | StrLit String         -- ^ string literal
              | KW    TokenKW         -- ^ keyword
              | Op    TokenOp         -- ^ operator
              | Sym   TokenSym        -- ^ symbol
              | Virt  TokenV          -- ^ virtual token (for layout)
              | White TokenW          -- ^ white space token
              | Err   TokenErr        -- ^ error token
              | EOF
                deriving (Eq,Show)

instance PP Token where
  ppPrec _ (Token _ s) = text s



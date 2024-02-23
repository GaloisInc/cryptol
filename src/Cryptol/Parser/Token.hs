{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE Safe #-}
module Cryptol.Parser.Token where

import Data.Text(Text)
import qualified Data.Text as Text
import Control.DeepSeq
import GHC.Generics

import Cryptol.Utils.PP

data Token    = Token { tokenType :: !TokenT, tokenText :: !Text }
                deriving (Show, Generic, NFData)

-- | Virtual tokens, inserted by layout processing.
data TokenV   = VCurlyL| VCurlyR | VSemi
                deriving (Eq, Show, Generic, NFData)

data TokenW   = BlockComment | LineComment | Space | DocStr
                deriving (Eq, Show, Generic, NFData)

data TokenKW  = KW_else
              | KW_fin
              | KW_if
              | KW_case
              | KW_of
              | KW_private
              | KW_include
              | KW_inf
              | KW_lg2
              | KW_lengthFromThen
              | KW_lengthFromThenTo
              | KW_max
              | KW_min
              | KW_module
              | KW_submodule
              | KW_newtype
              | KW_enum
              | KW_pragma
              | KW_property
              | KW_check
              | KW_prove
              | KW_sat
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
              | KW_interface
              | KW_foreign
              | KW_Prop
              | KW_by
              | KW_down
                deriving (Eq, Show, Generic, NFData)

-- | The named operators are a special case for parsing types, and 'Other' is
-- used for all other cases that lexed as an operator.
data TokenOp  = Plus | Minus | Mul | Div | Exp | Mod
              | Equal | LEQ | GEQ
              | Complement | Hash | At
              | Other [Text] Text
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
              | DotDotLt
              | DotDotGt
              | Colon
              | BackTick
              | ParenL   | ParenR
              | BracketL | BracketR
              | CurlyL   | CurlyR
              | TriL     | TriR
              | Lt | Gt
              | Underscore
                deriving (Eq, Show, Generic, NFData)

data TokenErr = UnterminatedComment
              | UnterminatedString
              | UnterminatedChar
              | InvalidString
              | InvalidChar
              | LexicalError
              | MalformedLiteral
              | MalformedSelector
              | InvalidIndentation TokenT -- expected closing paren
                deriving (Eq, Show, Generic, NFData)

data SelectorType = RecordSelectorTok Text | TupleSelectorTok Int
                deriving (Eq, Show, Generic, NFData)

data TokenT   = Num !Integer !Int !Int    -- ^ value, base, number of digits
              | Frac !Rational !Int       -- ^ value, base.
              | ChrLit  !Char             -- ^ character literal
              | Ident ![Text] !Text       -- ^ (qualified) identifier
              | StrLit !String            -- ^ string literal
              | Selector !SelectorType    -- ^ .hello or .123
              | KW    !TokenKW            -- ^ keyword
              | Op    !TokenOp            -- ^ operator
              | Sym   !TokenSym           -- ^ symbol
              | Virt  !TokenV             -- ^ virtual token (for layout)
              | White !TokenW             -- ^ white space token
              | Err   !TokenErr           -- ^ error token
              | EOF
                deriving (Eq, Show, Generic, NFData)

instance PP Token where
  ppPrec _ (Token _ s) = text (Text.unpack s)



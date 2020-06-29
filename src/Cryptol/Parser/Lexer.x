{
-- |
-- Module      :  Cryptol.Parser.Lexer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- At present Alex generates code with too many warnings.
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w #-}
module Cryptol.Parser.Lexer
  ( primLexer, lexer, Layout(..)
  , Token(..), TokenT(..)
  , TokenV(..), TokenKW(..), TokenErr(..), TokenSym(..), TokenW(..)
  , Located(..)
  , Config(..)
  , defaultConfig
  ) where

import Cryptol.Parser.Position
import Cryptol.Parser.LexerUtils
import Cryptol.Parser.Unlit(unLit)
import Data.Text (Text)
import qualified Data.Text as Text
}

$uniupper       = \x1
$unilower       = \x2
$unidigit       = \x3
$unisymbol      = \x4
$unispace       = \x5
$uniother       = \x6
$unitick        = \x7

@id_first     = [a-zA-Z_] | $unilower | $uniupper
@id_next      = [a-zA-Z0-9_'] | $unilower | $uniupper | $unidigit | $unitick

@id           = @id_first @id_next*
@op           = ([\!\#\$\%\&\*\+\-\.\/\:\<\=\>\?\@\\\^\|\~] | $unisymbol)+

@qual         = (@id ::)+
@qual_id      = @qual @id
@qual_op      = @qual @op

@num2         = "0b" (_*[0-1])+
@num8         = "0o" (_*[0-7])+
@num10        = [0-9](_*[0-9])*
@digits16     = (_*[0-9A-Fa-f])+
@num16        = "0x" @digits16
@fnum10       = @num10 "." @num10     ([eE] [\+\-]? @num10)?
@fnum16       = @num16 "." @digits16  ([pP] [\+\-]? @num10)?

@strPart      = [^\\\"]+
@chrPart      = [^\\\']+

:-

<0,comment> {
\/\*                     { startComment False }
\/\*\*                   { startComment True  }
\/\*\*\*+                { startComment False }
\/\*+\/                  { startEndComment    }
}

<comment> {
\*+\/                     { endComment }
[^\*\/]+                  { addToComment }
\*                        { addToComment }
\/                        { addToComment }
\n                        { addToComment }
}


<string> {
@strPart                  { addToString }
\"                        { endString }
\\.                       { addToString }
\n                        { endString }
}

<char> {
@chrPart                  { addToChar }
\'                        { endChar   }
\\.                       { addToChar }
\n                        { endChar   }
}


<0> {
$white+                   { emit $ White Space }
"//" .*                   { emit $ White LineComment }

@qual_id                  { mkQualIdent }
@qual_op                  { mkQualOp }

-- Please update the docs, if you add new entries.
"else"                    { emit $ KW KW_else }
"extern"                  { emit $ KW KW_extern }
"if"                      { emit $ KW KW_if }
"private"                 { emit $ KW KW_private }
"include"                 { emit $ KW KW_include }
"module"                  { emit $ KW KW_module }
"newtype"                 { emit $ KW KW_newtype }
"pragma"                  { emit $ KW KW_pragma }
"property"                { emit $ KW KW_property }
"then"                    { emit $ KW KW_then }
"type"                    { emit $ KW KW_type  }
"where"                   { emit $ KW KW_where }
"let"                     { emit $ KW KW_let }
"x"                       { emit $ KW KW_x }
"import"                  { emit $ KW KW_import }
"as"                      { emit $ KW KW_as }
"hiding"                  { emit $ KW KW_hiding }
"newtype"                 { emit $ KW KW_newtype }

"infixl"                  { emit $ KW KW_infixl }
"infixr"                  { emit $ KW KW_infixr }
"infix"                   { emit $ KW KW_infix  }

"primitive"               { emit $ KW KW_primitive }
"parameter"               { emit $ KW KW_parameter }
"constraint"              { emit $ KW KW_constraint }

"Prop"                    { emit $ KW KW_Prop }

@num2                     { emitS (numToken 2  . Text.drop 2) }
@num8                     { emitS (numToken 8  . Text.drop 2) }
@num10                    { emitS (numToken 10 . Text.drop 0) }
@num16                    { emitS (numToken 16 . Text.drop 2) }
@fnum10                   { emitS (fnumToken 10 . Text.drop 0) }
@fnum16                   { emitS (fnumToken 16 . Text.drop 2) }



"_"                       { emit $ Sym Underscore }
@id                       { mkIdent }

"\"                       { emit $ Sym Lambda }
"->"                      { emit $ Sym ArrR }
"<-"                      { emit $ Sym ArrL }
"=>"                      { emit $ Sym FatArrR }

"="                       { emit $ Sym EqDef }
","                       { emit $ Sym Comma }
";"                       { emit $ Sym Semi }
"."                       { emit $ Sym Dot }
":"                       { emit $ Sym Colon }
"`"                       { emit $ Sym BackTick }
".."                      { emit $ Sym DotDot }
"..."                     { emit $ Sym DotDotDot }
"|"                       { emit $ Sym Bar }
"("                       { emit $ Sym ParenL }
")"                       { emit $ Sym ParenR }
"["                       { emit $ Sym BracketL }
"]"                       { emit $ Sym BracketR }
"{"                       { emit $ Sym CurlyL }
"}"                       { emit $ Sym CurlyR }
"<|"                      { emit $ Sym TriL }
"|>"                      { emit $ Sym TriR }

\"                        { startString }
\'                        { startChar }

-- special cases for types and kinds
"+"                       { emit  (Op   Plus ) }
"-"                       { emit  (Op   Minus) }
"*"                       { emit  (Op   Mul  ) }
"^^"                      { emit  (Op   Exp  ) }

-- hash is used as a kind, and as a pattern
"#"                       { emit  (Op   Hash ) }

-- at-sign is used in declaration bindings
"@"                       { emit  (Op   At   ) }

-- ~ is used for unary complement
"~"                       { emit  (Op   Complement) }

-- all other operators
@op                       { emitS (Op . Other []) }
}


{
-- This code is here because it depends on `comment`, which is defined
-- in this file.

stateToInt :: LexS -> Int
stateToInt Normal         = 0
stateToInt (InComment {}) = comment
stateToInt (InString {})  = string
stateToInt (InChar {})    = char

-- | Returns the tokens in the last position of the input that we processed.
-- White space is removed, and layout processing is done as requested.
-- This stream is fed to the parser.
lexer :: Config -> Text -> ([Located Token], Position)
lexer cfg cs = ( case cfgLayout cfg of
                   Layout   -> layout cfg lexemes
                   NoLayout -> lexemes
               , finalPos
               )
  where (lex0, finalPos) = primLexer cfg cs
        lexemes          = dropWhite lex0

-- | Returns the tokens and the last position of the input that we processed.
-- The tokens include whte space tokens.
primLexer :: Config -> Text -> ([Located Token], Position)
primLexer cfg cs = run inp Normal
  where
  inp = Inp { alexPos           = start
            , alexInputPrevChar = '\n'
            , input             = unLit (cfgPreProc cfg) cs }

  singleR p = Range p p (cfgSource cfg)

  eofR p = Range p' p' (cfgSource cfg)
    where
    p' = Position { line = line p + 1, col = 0 }

  run i s =
    case alexScan i (stateToInt s) of
      AlexEOF ->
        case s of
          Normal        -> ([ Located (eofR $ alexPos i) (Token EOF "end of file") ]
                           , alexPos i
                           )
          InComment _ p _ _ ->
              ( [ Located (singleR p)
                $ Token (Err UnterminatedComment) "unterminated comment"
                ]
              , alexPos i)
          InString p _ ->
              ( [ Located (singleR p)
                $ Token (Err UnterminatedString) "unterminated string"
                ]
              , alexPos i)
          InChar p _ ->
              ( [ Located (singleR p)
                $ Token (Err UnterminatedChar) "unterminated character"
                ]
              , alexPos i)

      AlexError i'  ->
          let bad = Text.take 1 (input i)
          in
          ( [ Located (Range (alexPos i) (alexPos i') (cfgSource cfg))
               $ Token (Err LexicalError) bad ]
          , alexPos i')
      AlexSkip i' _ -> run i' s
      AlexToken i' l act ->
        let txt         = Text.take l (input i)
            (mtok,s')   = act cfg (alexPos i) txt s
            (rest,pos)  = run i' $! s'
        in case mtok of
             Nothing  -> (rest, pos)
             Just t   -> (t : rest, pos)

-- vim: ft=haskell
}

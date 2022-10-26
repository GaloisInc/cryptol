" Cryptol syntax file
" Language:     cryptol
" Author:       Iavor S. Diatchki

if exists("b:current_syntax")
  finish
endif

syn keyword cryKeywordImport import
syn keyword cryKeywordImport include

syn keyword cryKeyword module
syn keyword cryKeyword private
syn keyword cryKeyword infixl
syn keyword cryKeyword infixr
syn keyword cryKeyword infix
syn keyword cryKeyword submodule
syn keyword cryKeyword interface
syn keyword cryKeyword foreign
syn keyword cryKeyword newtype
syn keyword cryKeyword type
syn keyword cryKeyword primitive
syn keyword cryKeyword parameter
syn keyword cryKeyword constraint
syn keyword cryKeyword property
syn keyword cryKeyword if
syn keyword cryKeyword then
syn keyword cryKeyword else
syn keyword cryKeyword where
syn keyword cryKeyword let
syn keyword cryKeyword pragma
syn keyword cryKeyword down
syn keyword cryKeyword by

syn keyword cryKeywordType Prop
syn keyword cryKeywordType Bit Bool Word Char String Integer Z Rational
syn keyword cryKeywordType inf
syn keyword cryKeywordType Literal FLiteral LiteralLessThan
syn keyword cryKeywordType Zero Logic Ring Integral Field Round Eq Cmp SignedCmp
syn keyword cryKeywordType fin prime width lg2

syn keyword cryKeywordConst False True zero
syn keyword cryKeywordFun   min max abs
syn keyword cryKeywordFun   length
syn keyword cryKeywordFun   complement negate
syn keyword cryKeywordFun   fromInteger toInteger toSignedInteger fromZ
syn keyword cryKeywordFun   recip
syn keyword cryKeywordFun   error undefined assert
syn keyword cryKeywordFun   ceiling floor trunc roundAway roundToEven
syn keyword cryKeywordFun   carry scarry sborrow zext sext ratio
syn keyword cryKeywordFun   splitAt join split groupBy
syn keyword cryKeywordFun   reverse transpose take drop
syn keyword cryKeywordFun   head tail last
syn keyword cryKeywordFun   update updates updateEnd updatesEnd
syn keyword cryKeywordFun   generate
syn keyword cryKeywordFun   sort sortBy
syn keyword cryKeywordFun   pmult pdiv pmod
syn keyword cryKeywordFun   parmap
syn keyword cryKeywordFun   deepseq rnf
syn keyword cryKeywordFun   random trace traceVal
syn keyword cryKeywordFun   and or all any
syn keyword cryKeywordFun   map foldl foldr sum product scanl scanr elem
syn keyword cryKeywordFun   repeat iterate
syn keyword cryKeywordFun   zip zipWith
syn keyword cryKeywordFun   curry uncurry

syn match cryOperator "!"
syn match cryOperator "!!"
syn match cryOperator "@"
syn match cryOperator "@@"

syn match cryOperator "+"
syn match cryOperator "-"
syn match cryOperator "*"
syn match cryOperator "/"
syn match cryOperator "%"
syn match cryOperator "\^"
syn match cryOperator "/\^"
syn match cryOperator "/\."
syn match cryOperator "/\$"
syn match cryOperator "%\$"
syn match cryOperator "\^\^"

syn match cryOperator ">"
syn match cryOperator "<"
syn match cryOperator "!="
syn match cryOperator ">="
syn match cryOperator "<="
syn match cryOperator "<\$"
syn match cryOperator ">\$"
syn match cryOperator "<=\$"
syn match cryOperator ">=\$"
syn match cryOperator "!=="

syn match cryOperator ">>"
syn match cryOperator ">>\$"
syn match cryOperator "<<"
syn match cryOperator ">>>"
syn match cryOperator "<<<"

syn match cryOperator "#"

syn match cryOperator "&&"
syn match cryOperator "||"
syn match cryOperator "\\/"
syn match cryOperator "/\\"

syn match cryDelimiter ","
syn match cryDelimiter "`"
syn match cryDelimiter "\.\."
syn match cryDelimiter "\.\.\."
syn match cryDelimiter ":"
syn match cryDelimiter "("
syn match cryDelimiter ")"
syn match cryDelimiter "{"
syn match cryDelimiter "}"
syn match cryDelimiter "\["
syn match cryDelimiter "|"
syn match cryDelimiter "\]"
syn match cryDelimiter "="
syn match cryDelimiter "<-"

" Needs to be after =
syn match cryOperator "=="
syn match cryOperator "==="
syn match cryOperator "==>"

syn match   cryLineComment      "//.*$"
syn region  cryBlockComment     start="/\*" end="\*/" contains=cryBlockComment



syn match   cryEsc contained "\\\""
syn match   cryEsc contained "\\'"
syn match   cryEsc contained "\\\\"
syn match   cryEsc contained "\\n"
syn match   cryEsc contained "\\t"
syn match   cryEsc contained "\\r"
syn match   cryEsc contained "\\\d\+"
syn match   cryEsc contained "\\\(x\|X\)\x\+"
syn region  cryString start="\"" skip="\\\"" end="\"" contains=cryEsc
syn region  cryByte   start="'"  skip="\\'"  end="'"  contains=cryEsc


syn match   cryNumber "\(0\(x\|X\|b\|B\|o\|O\)\x\+\)\|-\?\(\d\|_\)\+"


" This is here so that we don't highlight numbers in X23 for example
" or x'
syn match ddlIdent "\(\l\|\u\)\(\a\|\d\|_\|'\)*"


hi def link cryKeywordImport  Include
hi def link cryKeyword        Structure

hi def link cryKeywordFun     Keyword
hi def link cryKeywordConst   Constant
hi def link cryKeywordType    Keyword

hi def link cryOperator       Operator
hi def link cryDelimiter      Delimiter

hi def link cryString         String
hi def link cryByte           String
hi def link cryEsc            Special

hi def link cryNumber         Number

hi def link cryLineComment    Comment
hi def link cryBlockComment   Comment

let b:current_syntax = "cryptol"

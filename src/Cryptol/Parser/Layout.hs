{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
module Cryptol.Parser.Layout where

import Cryptol.Utils.Panic(panic)
import Cryptol.Parser.Position
import Cryptol.Parser.Token

{-

We assume the existence of an explicit EOF token at the end of the input.  This token is *less* indented
than all other tokens (i.e., it is at column 0)

Explicit Layout Blocks

  * The symbols `(`, `{`, and `[` start an explicit layout block.
  * While in an explicit layout block we pass through tokens, except:
      - We may start new implicit or explicit layout blocks
      - A `,` terminates any *nested* layout blocks
      - We terminate the current layout block if we encounter the matching
        closing symbol `)`, `}`, `]`

Implicit Layout Blocks

  * The keywords `where`, `private`, and `parameter` start an implicit
    layout block.
  * The layout block starts at the column of the *following* token and we
    insert "virtual start block" between the current and the following tokens.
  * While in an implicit layout block:
    - We may start new implicit or explicit layout blocks
    - We insert a "virtual separator" before tokens starting at the same
      column as the layout block, EXCEPT:
        * we do not insert a separator if the previous token was a
          "documentation comment"
        * we do not insert a separator before the first token in the block

    - The implicit layout block is ended by:
          * a token than is less indented that the block, or
          * `)`, `}`, `]`, or
          * ',' but only if there is an outer paren block
          block's column.
    - When an implicit layout block ends, we insert a "virtual end block"
      token just before the token that caused the block to end.

Examples:

f = x where x = 0x1         -- end implicit layout by layout
g = 0x3                     -- (`g` is less indented than `x`)

f (x where x = 2)           -- end implicit layout by `)`

[ x where x = 2, 3 ]        -- end implicit layout by `,`

module A where              -- two implicit layout blocks with the
private                     -- *same* indentation (`where` and `private`)
x = 0x2
-}


layout :: Bool -> [Located Token] -> [Located Token]
layout isMod ts0

  -- Star an implicit layout block at the top of the module
  | let t         = head ts0
        rng       = srcRange t
        blockCol  = max 1 (col (from rng)) -- see startImplicitBlock
        implictMod = case map (tokenType . thing) ts0 of
                       KW KW_module : _                   -> False
                       KW KW_interface : KW KW_module : _ -> False
                       _                                  -> True
  , isMod && implictMod =
    virt rng VCurlyL : go [ Virtual blockCol ] blockCol True ts0

  | otherwise =
    go [] 0 False ts0

  where

  {- State parameters for `go`:

       stack:
          The stack of implicit and explicit blocks

       lastVirt:
          The indentation of the outer most implicit block, or 0 if none.
          This can be computed from the stack but we cache
          it here as we need to check it on each token.

       noVirtSep:
          Do not emit a virtual separator even if token matches block alignment.
          This is enabled at the beginning of a block, or after a doc string,
          or if we just emitted a separtor, but have not yet consumed the
          next token.

       tokens:
          remaining tokens to process
  -}

  go stack lastVirt noVirtSep tokens

    -- End implicit layout due to indentation.  If the outermost block
    -- is a lyout block we just end it.   If the outermost block is an
    -- explicit layout block we report a lexical error.
    | col curLoc < lastVirt =
      endImplictBlock

    -- End implicit layout block due to a symbol
    | Just (Virtual {}) <- curBlock, endsLayout curTokTy =
      endImplictBlock

    -- End implicit layout block due to a comma
    | Just (Virtual {}) <- curBlock
    , Sym Comma <- curTokTy
    , not (null [ () | Explicit _ <- popStack ]) =
      endImplictBlock

    -- Insert a virtual separator
    | Just (Virtual {}) <- curBlock
    , col curLoc == lastVirt && not noVirtSep =
      virt curRange VSemi : go stack lastVirt True tokens

    -- Start a new implicit layout. Advances token position.
    | startsLayout curTokTy = startImplicitBlock

    -- Start a paren block.  Advances token position
    | Just close <- startsParenBlock curTokTy =
      curTok : go (Explicit close : stack) lastVirt False advanceTokens

    -- End a paren block. Advances token position
    | Just (Explicit close) <- curBlock, close == curTokTy =
      curTok : go popStack lastVirt False advanceTokens

    -- Disable virtual separator after doc string. Advances token position
    | White DocStr <- curTokTy =
      curTok : go stack lastVirt True advanceTokens

    -- Check to see if we are done.  Note that if we got here, implicit layout
    -- blocks should have already been closed, as `EOF` is less indented than
    -- all other tokens
    | EOF <- curTokTy =
      [curTok]

    -- Any other token, just emit.  Advances token position
    | otherwise =
      curTok : go stack lastVirt False advanceTokens

    where
    (curTok, advanceTokens) = case tokens of
                                (curTok' : advanceTokens') -> (curTok', advanceTokens')
                                [] -> error "layout: Unexpected empty list of tokens"
    curTokTy               = tokenType (thing curTok)
    curRange               = srcRange curTok
    curLoc                 = from curRange

    (curBlock,popStack) =
      case stack of
        a : b -> (Just a,b)
        []    -> (Nothing, panic "layout" ["pop empty stack"])


    startImplicitBlock =
      let nextRng  = srcRange (head advanceTokens)
          nextLoc  = from nextRng
          blockCol = max 1 (col nextLoc)
          -- the `max` ensuraes that indentation is always at least 1,
          -- in case we are starting a block at the very end of the input

      in curTok
       : virt nextRng VCurlyL
       : go (Virtual blockCol : stack) blockCol True advanceTokens


    endImplictBlock =
      case curBlock of
        Just (Virtual {}) ->
           virt curRange VCurlyR
           : go popStack newVirt False tokens
          where newVirt = case [ n | Virtual n <- popStack ] of
                            n : _ -> n
                            _     -> 0

        Just (Explicit c) ->
          errTok curRange (InvalidIndentation c) : advanceTokens

        Nothing -> panic "layout" ["endImplictBlock with empty stack"]


--------------------------------------------------------------------------------

data Block =
    Virtual Int     -- ^ Virtual layout block
  | Explicit TokenT -- ^ An explicit layout block, expecting this ending token.
    deriving (Show)

-- | These tokens start an implicit layout block
startsLayout :: TokenT -> Bool
startsLayout ty =
  case ty of
    KW KW_where       -> True
    KW KW_private     -> True
    KW KW_parameter   -> True
    _                 -> False

-- | These tokens end an implicit layout block
endsLayout :: TokenT -> Bool
endsLayout ty =
  case ty of
    Sym BracketR -> True
    Sym ParenR   -> True
    Sym CurlyR   -> True
    _            -> False

-- | These tokens start an explicit "paren" layout block.
-- If so, the result contains the corresponding closing paren.
startsParenBlock :: TokenT -> Maybe TokenT
startsParenBlock ty =
  case ty of
    Sym BracketL -> Just (Sym BracketR)
    Sym ParenL   -> Just (Sym ParenR)
    Sym CurlyL   -> Just (Sym CurlyR)
    _            -> Nothing


--------------------------------------------------------------------------------

-- | Make a virtual token of the given type
virt :: Range -> TokenV -> Located Token
virt rng x = Located { srcRange = rng { to = from rng }, thing = t }
  where
  t = Token (Virt x)
      case x of
        VCurlyL -> "beginning of layout block"
        VCurlyR -> "end of layout block"
        VSemi   -> "layout block separator"

errTok :: Range -> TokenErr -> Located Token
errTok rng x = Located { srcRange = rng { to = from rng }, thing = t }
  where
  t = Token { tokenType = Err x, tokenText = "" }





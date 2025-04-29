-- |
-- Module      :  Cryptol.TypeCheck.Docstrings
-- Copyright   :  (c) 2013-2025 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE OverloadedStrings #-}
module Cryptol.TypeCheck.Docstrings where

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name
import Cryptol.Parser.AST (ImpName (..))
import Cryptol.TypeCheck.AST (Decl(..), Module, ModuleG(..), Pragma(..),
                              Submodule(..),  groupDecls)
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type
import Cryptol.Utils.Ident (identText)
import Cryptol.Utils.Panic (panic)

import           Data.Map  (Map)
import qualified Data.Map  as Map
import           Data.Maybe (fromMaybe, maybeToList)
import           Data.Text (Text)
import qualified Data.Text as T

data DocItem = DocItem
  { docModContext :: ImpName Name -- ^ The module scope to run repl commands in
  , docFor        :: DocFor -- ^ The name the documentation is attached to
  , docText       :: [Text] -- ^ The text of the attached docstring, if any
  }

data DocFor
  = DocForMod (ImpName Name)
  | DocForDef Name -- definitions that aren't modules

instance PP DocFor where
  ppPrec p x =
    case x of
      DocForMod m -> ppPrec p m
      DocForDef n -> ppPrec p n 


gatherModuleDocstrings ::
  Map Name (ImpName Name) ->
  Module ->
  [DocItem]
gatherModuleDocstrings nameToModule m =
  [DocItem
    { docModContext = ImpTop (mName m)
    , docFor = DocForMod (ImpTop (mName m))
    , docText = mDoc m
    }
  ] ++
  -- mParams m
  -- mParamTypes m
  -- mParamFuns m
  [DocItem
    { docModContext = lookupModuleName n
    , docFor = DocForDef n
    , docText = maybeToList (tsDoc t)
    } | (n, t) <- Map.assocs (mTySyns m)] ++
  [DocItem
    { docModContext = lookupModuleName n
    , docFor = DocForDef n
    , docText = maybeToList (ntDoc t)
    } | (n, t) <- Map.assocs (mNominalTypes m)] ++
  [DocItem
    { docModContext = lookupModuleName (dName d)
    , docFor = DocForDef (dName d)
    , docText = maybeToList (dDoc d <> exhaustBoolProp d)
    } | g <- mDecls m, d <- groupDecls g] ++
  [DocItem
    { docModContext = ImpNested n
    , docFor = DocForMod (ImpNested n)
    , docText = ifsDoc (smIface s)
    } | (n, s) <- Map.assocs (mSubmodules m)] ++
  [DocItem
    { docModContext = ImpTop (mName m)
    , docFor = DocForMod (ImpNested n)
    , docText = maybeToList (mpnDoc s)
    } | (n, s) <- Map.assocs (mSignatures m)]
  where
    lookupModuleName n =
      case Map.lookup n nameToModule of
        Just x -> x
        Nothing -> panic "gatherModuleDocstrings" ["No owning module for name:", show (pp n)]

    exhaustBoolProp d =
      if (null . extractCodeBlocks . fromMaybe "" . dDoc) d &&
         (tIsBit . sType . dSignature) d &&
         PragmaProperty `elem` dPragmas d
      then Just $ "```\n" <> ":exhaust " <> (identText . nameIdent) (dName d) <> " // implicit" <> "\n```"
      else Nothing

-- | Extract the code blocks from the body of a docstring.
--
-- A single code block starts with at least 3 backticks followed by an
-- optional language specifier of \"cryptol\". This allows other kinds
-- of code blocks to be included (and ignored) in docstrings. Longer
-- backtick sequences can be used when a code block needs to be able to
-- contain backtick sequences.
--
-- @
-- /**
--  * A docstring example
--  *
--  * ```cryptol
--  * :check example
--  * ```
--  */
-- @
extractCodeBlocks :: Text -> [[Text]]
extractCodeBlocks raw = go [] (T.lines raw)
  where
    go finished [] = reverse finished
    go finished (x:xs)
      | (spaces, x1) <- T.span (' ' ==) x
      , (ticks, x2) <- T.span ('`' ==) x1
      , 3 <= T.length ticks
      , not (T.elem '`' x2)
      , let info = T.strip x2
      = if info `elem` ["", "repl"] -- supported languages "unlabeled" and repl
        then keep finished (T.length spaces) (T.length ticks) [] xs
        else skip finished ticks xs
      | otherwise = go finished xs

    -- process a code block that we're keeping
    keep finished _ _ acc [] = go (reverse acc : finished) [] -- unterminated code fences are defined to be terminated by github
    keep finished indentLen ticksLen acc (x:xs)
      | x1 <- T.dropWhile (' ' ==) x
      , (ticks, x2) <- T.span ('`' ==) x1
      , ticksLen <= T.length ticks
      , T.all (' ' ==) x2
      = go (reverse acc : finished) xs

      | otherwise =
        let x' =
              case T.span (' ' ==) x of
                (spaces, x1)
                  | T.length spaces <= indentLen -> x1
                  | otherwise -> T.drop indentLen x
        in keep finished indentLen ticksLen (x' : acc) xs

    -- process a code block that we're skipping
    skip finished _ [] = go finished []
    skip finished close (x:xs)
      | close == x = go finished xs
      | otherwise = skip finished close xs


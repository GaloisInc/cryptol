-- |
-- Module      :  Cryptol.Parser.Selector
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Parser.Selector
  ( Selector(..)
  , ppSelector
  , ppNestedSels
  , selName
  ) where

import GHC.Generics (Generic)
import Control.DeepSeq
import Data.List(intersperse)

import Cryptol.Utils.Ident
import Cryptol.Utils.PP


{- | Selectors are used for projecting from various components.
Each selector has an option spec to specify the shape of the thing
that is being selected.  Currently, there is no surface syntax for
list selectors, but they are used during the desugaring of patterns.
-}

data Selector = TupleSel Int   (Maybe Int)
                -- ^ Zero-based tuple selection.
                -- Optionally specifies the shape of the tuple (one-based).

              | RecordSel Ident (Maybe [Ident])
                -- ^ Record selection.
                -- Optionally specifies the shape of the record.

              | ListSel Int    (Maybe Int)
                -- ^ List selection.
                -- Optionally specifies the length of the list.
                deriving (Eq, Show, Ord, Generic, NFData)

instance PP Selector where
  ppPrec _ sel =
    case sel of
      TupleSel x sig    -> int x <+> ppSig tupleSig sig
      RecordSel x sig  -> pp x  <+> ppSig recordSig sig
      ListSel x sig    -> int x <+> ppSig listSig sig

    where
    tupleSig n   = int n
    recordSig xs = braces $ fsep $ punctuate comma $ map pp xs
    listSig n    = int n

    ppSig f = maybe empty (\x -> text "/* of" <+> f x <+> text "*/")


-- | Display the thing selected by the selector, nicely.
ppSelector :: Selector -> Doc
ppSelector sel =
  case sel of
    TupleSel x _  -> ordinal (x+1) <+> text "field"
    RecordSel x _ -> text "field" <+> pp x
    ListSel x _   -> ordinal x <+> text "element"

-- | The name of a selector (e.g., used in update code)
selName :: Selector -> Ident
selName s =
  case s of
    RecordSel i _ -> i
    TupleSel n _  -> packIdent ("_" ++ show n)
    ListSel n _   -> packIdent ("__" ++ show n)

-- | Show a list of selectors as they appear in a nested selector in an update.
ppNestedSels :: [Selector] -> Doc
ppNestedSels = hcat . intersperse "." . map ppS
  where ppS s = case s of
                  RecordSel i _ -> text (unpackIdent i)
                  TupleSel n _ -> int n
                  ListSel n _  -> brackets (int n) -- not in source

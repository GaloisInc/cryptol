-- |
-- Module      :  Cryptol.Parser.Fixity
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Parser.Fixity
  ( Fixity(..)
  , defaultFixity
  , FixityCmp(..)
  , compareFixity
  ) where

import Cryptol.Utils.PP

import GHC.Generics (Generic)
import Control.DeepSeq

data Fixity = Fixity { fAssoc :: !Assoc
                     , fLevel :: !Int
                     } deriving (Eq, Generic, NFData, Show)

data FixityCmp = FCError
               | FCLeft
               | FCRight
                 deriving (Show, Eq)

compareFixity :: Fixity -> Fixity -> FixityCmp
compareFixity (Fixity a1 p1) (Fixity a2 p2) =
  case compare p1 p2 of
    GT -> FCLeft
    LT -> FCRight
    EQ -> case (a1, a2) of
            (LeftAssoc, LeftAssoc)   -> FCLeft
            (RightAssoc, RightAssoc) -> FCRight
            _                        -> FCError

-- | The fixity used when none is provided.
defaultFixity :: Fixity
defaultFixity = Fixity LeftAssoc 100

instance PP Fixity where
  ppPrec _ (Fixity assoc level) =
    text "precedence" <+> int level <.> comma <+> pp assoc

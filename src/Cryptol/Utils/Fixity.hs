-- |
-- Module      :  Cryptol.Utils.Fixity
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Utils.Fixity
  ( Assoc(..)
  , Fixity(..)
  , defaultFixity
  , FixityCmp(..)
  , compareFixity
  ) where

import GHC.Generics (Generic)
import Control.DeepSeq

-- | Information about associativity.
data Assoc = LeftAssoc | RightAssoc | NonAssoc
  deriving (Show, Eq, Ord, Generic, NFData)

data Fixity = Fixity { fAssoc :: !Assoc, fLevel :: !Int }
  deriving (Eq, Ord, Generic, NFData, Show)

data FixityCmp = FCError
               | FCLeft
               | FCRight
                 deriving (Show, Eq)

-- | Let @op1@ have fixity @f1@ and @op2@ have fixity @f2. Then
-- @compareFixity f1 f2@ determines how to parse the infix expression
-- @x op1 y op2 z@.
--
-- * @FCLeft@: @(x op1 y) op2 z@
-- * @FCRight@: @x op1 (y op2 z)@
-- * @FCError@: no parse
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

{-# LANGUAGE OverloadedStrings #-}

-- | Some utility functions for conveniently building up Cryptol Parser AST data
-- structures in Haskell. This isn't currently used by Cryptol itself but can be
-- used by other tools that need to manipulate Cryptol ASTs like SAW.
--
-- This module is intended to be imported qualified.
module Cryptol.Parser.AST.Builder where

import qualified Data.Text          as Text
import           Numeric.Natural

import           Cryptol.Parser.AST

-- * Built-in syntax

-- | Polymorphic integer literal. For negative inputs, a prefix negation
-- operator will be added.
--
-- @intLit n@ is equivalent to the literal @n@ in Cryptol.
intLit :: Integral a => a -> Expr n
intLit n =
  let n' = toInteger n
  in  (if n' < 0 then EPrefix PrefixNeg else id) $
        ELit $ ECNum (abs n') $ DecLit $ Text.pack $ show (abs n')

-- | Integer literal as a bitvector of a specific width.
--
-- @bvLit n m@ is equivalent to the type-annotated literal @n : [m]@ in Cryptol.
bvLit :: Natural -> Natural -> Expr PName
bvLit val bits =
  number (TNum (toInteger val)) (TSeq (TNum (toInteger bits)) TBit)

-- * Cryptol prelude functions lifted to Haskell

-- | Cryptol @number@ lifted to Haskell.
number :: Type PName -> Type PName -> Expr PName
number = funT2 "number"

-- | Cryptol @(<=)@ lifted to Haskell.
(<=) :: Expr PName -> Expr PName -> Expr PName
(<=) = funV2 (mkInfix "<=")
infix 4 <=

-- | Cryptol @(>=)@ lifted to Haskell.
(>=) :: Expr PName -> Expr PName -> Expr PName
(>=) = funV2 (mkInfix ">=")
infix 4 >=

-- * Lower level utilities

-- | Lift a Cryptol named function with 2 value parameters to Haskell.
funV2 :: Ident -> Expr PName -> Expr PName -> Expr PName
funV2 f x y = var f $$ x $$ y

-- | Lift a Cryptol named polymorphic value with 2 type parameters to Haskell.
funT2 :: Ident -> Type PName -> Type PName -> Expr PName
funT2 f a b = var f $^ [PosInst a, PosInst b]

-- | Create an unqualified variable expression from an identifier.
var :: Ident -> Expr PName
var = EVar . mkUnqual

-- | Infix operator for Cryptol value application.
($$) :: Expr n -> Expr n -> Expr n
($$) = EApp
infixl 1 $$

-- | Infix operator for Cryptol type application.
($^) :: Expr n -> [TypeInst n] -> Expr n
($^) = EAppT
infixl 2 $^

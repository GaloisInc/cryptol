-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.Boolean
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Abstraction of booleans. Unfortunately, Haskell makes Bool's very hard to
-- work with, by making it a fixed-data type. This is our workaround
-----------------------------------------------------------------------------

module Data.SBV.Utils.Boolean(Boolean(..), bAnd, bOr, bAny, bAll)  where

infixl 6 <+>       -- xor
infixr 3 &&&, ~&   -- and, nand
infixr 2 |||, ~|   -- or, nor
infixr 1 ==>, <=>  -- implies, iff

-- | The 'Boolean' class: a generalization of Haskell's 'Bool' type
-- Haskell 'Bool' and SBV's 'SBool' are instances of this class, unifying the treatment of boolean values.
--
-- Minimal complete definition: 'true', 'bnot', '&&&'
-- However, it's advisable to define 'false', and '|||' as well (typically), for clarity.
class Boolean b where
  -- | logical true
  true   :: b
  -- | logical false
  false  :: b
  -- | complement
  bnot   :: b -> b
  -- | and
  (&&&)  :: b -> b -> b
  -- | or
  (|||)  :: b -> b -> b
  -- | nand
  (~&)   :: b -> b -> b
  -- | nor
  (~|)   :: b -> b -> b
  -- | xor
  (<+>)  :: b -> b -> b
  -- | implies
  (==>)  :: b -> b -> b
  -- | equivalence
  (<=>)  :: b -> b -> b
  -- | cast from Bool
  fromBool :: Bool -> b

  -- default definitions
  false   = bnot true
  a ||| b = bnot (bnot a &&& bnot b)
  a ~& b  = bnot (a &&& b)
  a ~| b  = bnot (a ||| b)
  a <+> b = (a &&& bnot b) ||| (bnot a &&& b)
  a <=> b = (a &&& b) ||| (bnot a &&& bnot b)
  a ==> b = bnot a ||| b
  fromBool True  = true
  fromBool False = false

-- | Generalization of 'and'
bAnd :: Boolean b => [b] -> b
bAnd = foldr (&&&) true

-- | Generalization of 'or'
bOr :: Boolean b => [b] -> b
bOr  = foldr (|||) false

-- | Generalization of 'any'
bAny :: Boolean b => (a -> b) -> [a] -> b
bAny f = bOr  . map f

-- | Generalization of 'all'
bAll :: Boolean b => (a -> b) -> [a] -> b
bAll f = bAnd . map f

instance Boolean Bool where
  true   = True
  false  = False
  bnot   = not
  (&&&)  = (&&)
  (|||)  = (||)

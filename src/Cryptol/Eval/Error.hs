-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Cryptol.Eval.Error where

import Cryptol.Utils.Panic
import Cryptol.Utils.PP
import Cryptol.TypeCheck.AST(Type)

import           Data.Typeable (Typeable)
import qualified Control.Exception as X


-- Errors ----------------------------------------------------------------------

-- | Panic from an Eval context.
evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Eval] " ++ cxt)


data EvalError
  = InvalidIndex Integer
  | TypeCannotBeDemoted Type
  | DivideByZero
  | WordTooWide Integer
  | UserError String
    deriving (Typeable,Show)

instance PP EvalError where
  ppPrec _ e = case e of
    InvalidIndex i -> text "invalid sequence index:" <+> integer i
    TypeCannotBeDemoted t -> text "type cannot be demoted:" <+> pp t
    DivideByZero -> text "division by 0"
    WordTooWide w ->
      text "word too wide for memory:" <+> integer w <+> text "bits"
    UserError x -> text "Run-time error:" <+> text x

instance X.Exception EvalError

-- | A sequencing operation has gotten an invalid index.
invalidIndex :: Integer -> a
invalidIndex i = X.throw (InvalidIndex i)

-- | For things like `(inf) or `(0-1)
typeCannotBeDemoted :: Type -> a
typeCannotBeDemoted t = X.throw (TypeCannotBeDemoted t)

-- | For division by 0.
divideByZero :: a
divideByZero = X.throw DivideByZero

-- | For when we know that a word is too wide and will exceed gmp's
-- limits (though words approaching this size will probably cause the
-- system to crash anyway due to lack of memory)
wordTooWide :: Integer -> a
wordTooWide w = X.throw (WordTooWide w)

-- | For `error`
cryUserError :: String -> a
cryUserError msg = X.throw (UserError msg)


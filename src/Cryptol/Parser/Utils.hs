-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Utility functions that are also useful for translating programs
-- from previous Cryptol versions.

module Cryptol.Parser.Utils
  ( translateExprToNumT
  ) where

import Cryptol.Parser.AST
import Cryptol.Parser.Position (at)
import Cryptol.Prims.Syntax

import qualified Data.Map as Map


translateExprToNumT :: Expr -> Maybe Type
translateExprToNumT expr =
  case expr of
    ELocated e r -> (`TLocated` r) `fmap` translateExprToNumT e
    EVar (QName Nothing (Name "width")) -> mkFun TCWidth
    EVar x       -> return (TUser x [])
    ELit x       -> cvtLit x
    EApp e1 e2   -> do t1 <- translateExprToNumT e1
                       t2 <- translateExprToNumT e2
                       tApp t1 t2

    EInfix a o b -> do e1 <- translateExprToNumT a
                       e2 <- translateExprToNumT b
                       ec <- cvtCon =<< Map.lookup (thing o) primNames
                       f  <- tApp (at o ec) e1
                       tApp f e2

    EParens e    -> translateExprToNumT e

    _            -> Nothing

  where
  tApp ty t =
    case ty of
      TLocated t1 r -> (`TLocated` r) `fmap` tApp t1 t
      TApp f ts     -> return (TApp f (ts ++ [t]))
      TUser f ts    -> return (TUser f (ts ++ [t]))
      _             -> Nothing

  mkFun f = return (TApp f [])

  cvtLit (ECNum n CharLit)  = return (TChar $ toEnum $ fromInteger n)
  cvtLit (ECNum n _)        = return (TNum n)
  cvtLit (ECString _)       = Nothing

  cvtCon c =
    case c of
      ECPlus        -> mkFun TCAdd
      ECMinus       -> mkFun TCSub
      ECMul         -> mkFun TCMul
      ECDiv         -> mkFun TCDiv
      ECMod         -> mkFun TCMod
      ECExp         -> mkFun TCExp
      ECLg2         -> mkFun TCLg2
      ECMin         -> mkFun TCMin
      ECMax         -> mkFun TCMax
      _             -> Nothing

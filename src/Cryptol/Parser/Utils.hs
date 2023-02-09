-- |
-- Module      :  Cryptol.Parser.Utils
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Utility functions that are also useful for translating programs
-- from previous Cryptol versions.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Safe #-}

module Cryptol.Parser.Utils
  ( translateExprToNumT
  , widthIdent
  ) where

import Cryptol.Parser.AST

widthIdent :: Ident
widthIdent  = mkIdent "width"

underIdent :: Ident
underIdent = mkIdent "_"

translateExprToNumT :: Expr PName -> Maybe (Type PName)
translateExprToNumT expr =
  case expr of
    ELocated e r -> (`TLocated` r) `fmap` translateExprToNumT e
    EVar n | getIdent n == widthIdent -> pure (TUser n [])
           | getIdent n == underIdent -> pure TWild
    EVar x       -> return (TUser x [])
    ELit x       -> cvtLit x
    EApp e1 e2   -> do t1 <- translateExprToNumT e1
                       t2 <- translateExprToNumT e2
                       tApp t1 t2

    EInfix a o f b -> do e1 <- translateExprToNumT a
                         e2 <- translateExprToNumT b
                         return (TInfix e1 o f e2)

    EParens e    -> do t <- translateExprToNumT e
                       return (TParens t Nothing)

    _            -> Nothing

  where
  tApp ty t =
    case ty of
      TLocated t1 r -> (`TLocated` r) `fmap` tApp t1 t
      TUser f ts    -> return (TUser f (ts ++ [t]))
      _             -> Nothing

  cvtLit (ECNum n _)        = return (TNum n)
  cvtLit (ECChar c)         = return (TChar c)
  cvtLit (ECFrac {})        = Nothing
  cvtLit (ECString _)       = Nothing

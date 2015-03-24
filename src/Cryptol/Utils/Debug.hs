-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
#define DEBUG

#ifdef DEBUG
{-# LANGUAGE Trustworthy #-}
#else
{-# LANGUAGE Safe #-}
#endif

module Cryptol.Utils.Debug where

import Cryptol.Utils.PP

#ifdef DEBUG
import qualified Debug.Trace as X
trace :: String -> b -> b
trace = X.trace
#else
trace :: String -> b -> b
trace _ x = x
#endif

ppTrace :: Doc -> b -> b
ppTrace d = trace (show d)


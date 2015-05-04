-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Architecture-specific parts of the concrete evaluator go here.
{-# LANGUAGE CPP #-}
module Cryptol.Eval.Arch where

-- | This is the widest word we can have before gmp will fail to
-- allocate and bring down the whole program. According to
-- <https://gmplib.org/list-archives/gmp-bugs/2009-July/001538.html>
-- the sizes are 2^32-1 for 32-bit, and 2^37 for 64-bit, however
-- experiments show that it's somewhere under 2^37 at least on 64-bit
-- Mac OS X.
maxBigIntWidth :: Integer
#if i386_HOST_ARCH
maxBigIntWidth = 2^(32 :: Integer) - 0x1
#elif x86_64_HOST_ARCH
maxBigIntWidth = 2^(37 :: Integer) - 0x100
#else
#error unknown max width for gmp on this architecture
#endif

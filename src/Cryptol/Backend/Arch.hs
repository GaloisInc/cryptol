-- |
-- Module      :  Cryptol.Eval.Arch
-- Copyright   :  (c) 2014-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Architecture-specific parts of the concrete evaluator go here.
{-# LANGUAGE CPP #-}
module Cryptol.Backend.Arch where

-- | This is the widest word we can have before gmp will fail to
-- allocate and bring down the whole program. According to
-- <https://gmplib.org/list-archives/gmp-bugs/2009-July/001538.html>
-- the sizes are 2^32-1 for 32-bit, and 2^37 for 64-bit, however
-- experiments show that it's somewhere under 2^37 at least on 64-bit
-- Mac OS X.
maxBigIntWidth :: Integer
#if defined(i386_HOST_ARCH)
maxBigIntWidth = 2^(32 :: Integer) - 0x1
#elif defined(x86_64_HOST_ARCH) || defined(aarch64_HOST_ARCH)
maxBigIntWidth = 2^(37 :: Integer) - 0x100
#else
-- Because GHC doesn't seem to define a CPP macro that will portably
-- tell us the bit width we're compiling for, fall back on a safe choice
-- for other architectures. If we care about large words on another
-- architecture, we can add a special case for it.
maxBigIntWidth = 2^(32 :: Integer) - 0x1
#endif

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable


module OptParser where

import Data.Monoid (Endo(..))

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid(..))
#endif

data OptParser opt
  = OptSuccess (Endo opt)
  | OptFailure [String]

instance Monoid (OptParser opt) where
  mempty = OptSuccess mempty
  l `mappend` r = case (l,r) of
    (OptSuccess f,OptSuccess g) -> OptSuccess (f `mappend` g)
    (OptFailure a,OptFailure b) -> OptFailure (a `mappend` b)
    (OptFailure _,_)            -> l
    (_,OptFailure _)            -> r

runOptParser :: opt -> OptParser opt -> Either [String] opt
runOptParser def parse = case parse of
  OptSuccess update -> Right (appEndo update def)
  OptFailure msgs   -> Left msgs

modify :: (opt -> opt) -> OptParser opt
modify f = OptSuccess (Endo f)

report :: String -> OptParser opt
report msg = OptFailure [msg]

-- |
-- Module      :  Cryptol.Utils.Misc
-- Copyright   :  (c) 2014-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Trustworthy, FlexibleContexts #-}
module Cryptol.Utils.Misc where

import MonadLib

import Prelude ()
import Prelude.Compat

-- | Apply a function to all elements of a container.
-- Returns `Nothing` if nothing changed, and @Just container@ otherwise.
anyJust :: Traversable t => (a -> Maybe a) -> t a -> Maybe (t a)
anyJust f m = mk $ runLift $ runStateT False $ traverse upd m
  where
  mk (a,changes) = if changes then Just a else Nothing

  upd x = case f x of
            Just y  -> set True >> return y
            Nothing -> return x

-- | Apply functions to both elements of a pair.
-- Returns `Nothing` if neither changed, and @Just pair@ otherwise.
anyJust2 :: (a -> Maybe a) -> (b -> Maybe b) -> (a,b) -> Maybe (a,b)
anyJust2 f g (a,b) =
  case (f a, g b) of
    (Nothing, Nothing) -> Nothing
    (Just x , Nothing) -> Just (x, b)
    (Nothing, Just y ) -> Just (a, y)
    (Just x , Just y ) -> Just (x, y)

{-# LANGUAGE Safe, FlexibleContexts #-}
module Cryptol.Utils.Misc where

import MonadLib
import Data.Maybe(fromMaybe)

import Prelude ()
import Prelude.Compat

-- | Apply a function to all elements of a container.
-- Returns `Nothing` if nothing changed, and @Just container@ otherwise.
anyJust :: Traversable t => (a -> Maybe a) -> t a -> Maybe (t a)
anyJust f m = mk $ runId $ runStateT False $ traverse upd m
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
    (x,y)              -> Just (fromMaybe a x, fromMaybe b y)

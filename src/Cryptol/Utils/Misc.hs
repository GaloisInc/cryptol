{-# LANGUAGE Safe #-}
module Cryptol.Utils.Misc where

import Data.Traversable (Traversable, traverse)
import MonadLib


-- | Apply a function to all elements of a container.
-- Returns `Nothing` if nothing changed, and @Just container@ otherwise.
anyJust :: Traversable t => (a -> Maybe a) -> t a -> Maybe (t a)
anyJust f m = mk $ runId $ runStateT False $ traverse upd m
  where
  mk (a,changes) = if changes then Just a else Nothing

  upd x = case f x of
            Just y  -> set True >> return y
            Nothing -> return x





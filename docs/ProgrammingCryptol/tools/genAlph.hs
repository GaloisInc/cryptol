-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

-- alph generates a random permutation of the alphabet
-- symAlph gives you a permutation that is symmetric (i.e., if A maps to B, then
-- B maps to A); and also one that never maps anything back to itself.
module GenAlph(alph, symAlph) where

import System.Random
import qualified Data.Map as M
import Control.Monad

letters = ['A' .. 'Z']

genAlph = go []
 where go xs | length xs == 26 = return xs
             | True           = do s <- randomRIO (0, 25)
                                   if s `elem` xs then go xs else go (s:xs)

alph = do s <- genAlph
          return $ [letters !! i | i <- s ]

symAlph = do s <- foldM add M.empty letters
             return $ map snd $ M.toAscList s
  where add m l
         | l `elem` M.keys m = return m
         | True              = do i <- randomRIO (0, 25)
                                  let e = letters !! i
                                  if e == l
                                     then add m l
                                     else case e `M.lookup` m of
                                           Nothing -> return $ M.insert l e $ M.insert e l $ m
                                           Just _  -> add m l

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module Cryptol.TypeCheck.TypeMap
  ( TypeMap(..), TypesMap, TrieMap(..)
  , insertTM, insertWithTM
  , membersTM

  , List(..)
  ) where

import           Cryptol.TypeCheck.AST

import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe(fromMaybe,maybeToList)
import           Control.Monad((<=<))
import           Data.List(sortBy,partition)
import           Data.Maybe (isNothing)
import           Data.Ord(comparing)

class TrieMap m k | m -> k where
  emptyTM  :: m a
  nullTM   :: m a -> Bool
  lookupTM :: k -> m a -> Maybe a
  alterTM  :: k -> (Maybe a -> Maybe a) -> m a -> m a
  unionTM  :: (a -> a -> a) -> m a -> m a -> m a
  toListTM :: m a -> [(k,a)]

membersTM :: TrieMap m k => m a -> [a]
membersTM  = map snd . toListTM

insertTM :: TrieMap m k => k -> a -> m a -> m a
insertTM t a = alterTM t (\_ -> Just a)

insertWithTM :: TrieMap m k => (a -> a -> a) -> k -> a -> m a -> m a
insertWithTM f t new = alterTM t $ \mb -> Just $ case mb of
                                                   Nothing  -> new
                                                   Just old -> f old new

data List m a  = L { nil  :: Maybe a
                   , cons :: m (List m a)
                   } deriving (Functor)

instance TrieMap m a => TrieMap (List m) [a] where
  emptyTM = L { nil = Nothing, cons = emptyTM }

  nullTM k = isNothing (nil k) && nullTM (cons k)

  lookupTM k =
    case k of
      []     -> nil
      x : xs -> lookupTM xs <=< lookupTM x . cons

  alterTM k f m =
    case k of
      []    -> m { nil = f (nil m) }
      x:xs  -> m { cons = alterTM x (updSub xs f) (cons m) }

  toListTM m =
    [ ([], v)  | v <- maybeToList (nil m) ] ++
    [ (x:xs,v) | (x,m1) <- toListTM (cons m), (xs,v) <- toListTM m1 ]

  unionTM f m1 m2 = L { nil  = case (nil m1, nil m2) of
                                 (Just x, Just y) -> Just (f x y)
                                 (Just x, _)      -> Just x
                                 (_, Just y)      -> Just y
                                 _                -> Nothing
                      , cons = unionTM (unionTM f) (cons m1) (cons m2)
                      }


instance Ord a => TrieMap (Map a) a where
  emptyTM  = Map.empty
  nullTM   = Map.null
  lookupTM = Map.lookup
  alterTM  = flip Map.alter
  toListTM = Map.toList
  unionTM  = Map.unionWith


type TypesMap = List TypeMap

data TypeMap a = TM { tvar :: Map TVar a
                    , tcon :: Map TCon   (List TypeMap a)
                    , trec :: Map [Name] (List TypeMap a)
                    } deriving (Functor)

instance TrieMap TypeMap Type where
  emptyTM = TM { tvar = emptyTM, tcon = emptyTM, trec = emptyTM }

  nullTM ty = and [ nullTM (tvar ty)
                  , nullTM (tcon ty)
                  , nullTM (trec ty) ]

  lookupTM ty =
    case ty of
      TUser _ _ t -> lookupTM t
      TVar x      -> lookupTM x . tvar
      TCon c ts   -> lookupTM ts <=< lookupTM c . tcon
      TRec fs     -> let (xs,ts) = unzip $ sortBy (comparing fst) fs
                     in lookupTM ts <=< lookupTM xs . trec

  alterTM ty f m =
    case ty of
      TUser _ _ t -> alterTM t f m
      TVar x      -> m { tvar = alterTM x f (tvar m) }
      TCon c ts   -> m { tcon = alterTM c (updSub ts f) (tcon m) }
      TRec fs     -> let (xs,ts) = unzip $ sortBy (comparing fst) fs
                     in m { trec = alterTM xs (updSub ts f) (trec m) }

  toListTM m =
    [ (TVar x,           v) | (x,v)   <- toListTM (tvar m) ] ++
    [ (TCon c ts,        v) | (c,m1)  <- toListTM (tcon m)
                            , (ts,v)  <- toListTM m1 ] ++
    [ (TRec (zip fs ts), v) | (fs,m1) <- toListTM (trec m)
                            , (ts,v)  <- toListTM m1 ]

  unionTM f m1 m2 = TM { tvar = unionTM f (tvar m1) (tvar m2)
                       , tcon = unionTM (unionTM f) (tcon m1) (tcon m2)
                       , trec = unionTM (unionTM f) (trec m1) (trec m2)
                       }


updSub :: TrieMap m k => k -> (Maybe a -> Maybe a) -> Maybe (m a) -> Maybe (m a)
updSub k f = Just . alterTM k f . fromMaybe emptyTM

instance Show a => Show (TypeMap a) where
  showsPrec p xs = showsPrec p (toListTM xs)


-- |
-- Module      :  Cryptol.Utils.RecordMap
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module implements an "order insensitive" datastructure for
-- record types and values.  For most purposes, we want to deal with
-- record fields in a canonical order; but for user interaction
-- purposes, we generally want to display the fields in the order they
-- were specified by the user (in source files, at the REPL, etc.).

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}

module Cryptol.Utils.RecordMap
  ( RecordMap
  , displayOrder
  , canonicalFields
  , displayFields
  , recordElements
  , displayElements
  , fieldSet
  , recordFromFields
  , recordFromFieldsErr
  , recordFromFieldsWithDisplay
  , lookupField
  , adjustField
  , traverseRecordMap
  , mapWithFieldName
  , zipRecordsM
  , zipRecords
  , recordMapAccum
  ) where

import           Control.DeepSeq
import           Control.Monad.Except
import           Data.Functor.Identity
import           Data.Set (Set)
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map

import Cryptol.Utils.Panic

-- | An "order insensitive" datastructure.
--   The fields can be accessed either according
--   to a "canonical" order, or based on a
--   "display" order, which matches the order
--   in which the fields were originally specified.
data RecordMap a b =
  RecordMap
  { recordMap :: !(Map a b)
  , _displayOrder :: [a]
  }
-- RecordMap Invariant:
--   The `displayOrder` field should contain exactly the
--   same set of field names as the keys of `recordMap`.
--   Moreover, each field name should occur at most once.

instance (Ord a, Eq b) => Eq (RecordMap a b) where
  a == b = recordMap a == recordMap b

instance (Ord a, Ord b) => Ord (RecordMap a b) where
  compare a b = compare (recordMap a) (recordMap b)

instance (Show a, Ord a, Show b) => Show (RecordMap a b) where
  show = show . displayFields

instance (NFData a, NFData b) => NFData (RecordMap a b) where
  rnf = rnf . canonicalFields


-- | Return the fields in this record as a set.
fieldSet :: Ord a => RecordMap a b -> Set a
fieldSet r = Map.keysSet (recordMap r)

-- | The order in which the fields originally appeared.
displayOrder :: RecordMap a b -> [a]
displayOrder r = _displayOrder r

-- | Retrieve the elements of the record in canonical order
--   of the field names
recordElements :: RecordMap a b -> [b]
recordElements = map snd . canonicalFields

-- | Return a list of field/value pairs in canonical order.
canonicalFields :: RecordMap a b -> [(a,b)]
canonicalFields = Map.toList . recordMap

-- | Retrieve the elements of the record in display order
--   of the field names.
displayElements :: (Show a, Ord a) => RecordMap a b -> [b]
displayElements = map snd . displayFields

-- | Return a list of field/value pairs in display order.
displayFields :: (Show a, Ord a) => RecordMap a b -> [(a,b)]
displayFields r = map find (displayOrder r)
  where
  find x =
    case Map.lookup x (recordMap r) of
      Just v -> (x, v)
      Nothing ->
         panic "displayFields"
               ["Could not find field in recordMap " ++ show x
               , "Display order: " ++ show (displayOrder r)
               , "Canonical order:" ++ show (map fst (canonicalFields r))
               ]

-- | Generate a record from a list of field/value pairs.
--   Precondition: each field identifier appears at most
--   once in the given list.
recordFromFields :: (Show a, Ord a) => [(a,b)] -> RecordMap a b
recordFromFields xs =
  case recordFromFieldsErr xs of
    Left (x,_) ->
          panic "recordFromFields"
                ["Repeated field value: " ++ show x]
    Right r -> r

-- | Generate a record from a list of field/value pairs.
--   If any field name is repeated, the first repeated name/value
--   pair is returned.  Otherwise the constructed record is returned.
recordFromFieldsErr :: (Show a, Ord a) => [(a,b)] -> Either (a,b) (RecordMap a b)
recordFromFieldsErr xs0 = loop mempty xs0
  where
  loop m [] = Right (RecordMap m (map fst xs0))
  loop m ((x,v):xs)
    | Just _ <- Map.lookup x m = Left (x,v)
    | otherwise = loop (Map.insert x v m) xs

-- | Generate a record from a list of field/value pairs,
--   and also provide the "display" order for the fields directly.
--   Precondition: each field identifier appears at most once in each
--   list, and a field name appears in the display order iff it appears
--   in the field list.
recordFromFieldsWithDisplay :: (Show a, Ord a) => [a] -> [(a,b)] -> RecordMap a b
recordFromFieldsWithDisplay dOrd fs = r { _displayOrder = dOrd }
  where
  r = recordFromFields fs

-- | Lookup the value of a field
lookupField :: Ord a => a -> RecordMap a b -> Maybe b
lookupField x m = Map.lookup x (recordMap m)

-- | Update the value of a field by applying the given function.
--   If the field is not present in the record, return Nothing.
adjustField :: forall a b. Ord a => a -> (b -> b) -> RecordMap a b -> Maybe (RecordMap a b)
adjustField x f r = mkRec <$> Map.alterF f' x (recordMap r)
  where
  mkRec m = r{ recordMap = m }

  f' :: Maybe b -> Maybe (Maybe b)
  f' Nothing = Nothing
  f' (Just v) = Just (Just (f v))

-- | Traverse the elements of the given record map in canonical
--   order, applying the given action.
traverseRecordMap :: Applicative t =>
  (a -> b -> t c) -> RecordMap a b -> t (RecordMap a c)
traverseRecordMap f r =
  (\m -> RecordMap m (displayOrder r)) <$> Map.traverseWithKey f (recordMap r)

-- | Apply the given function to each element of a record.
mapWithFieldName :: (a -> b -> c) -> RecordMap a b -> RecordMap a c
mapWithFieldName f = runIdentity . traverseRecordMap (\a b -> Identity (f a b))

instance Functor (RecordMap a) where
  fmap f = mapWithFieldName (\_ -> f)

instance Foldable (RecordMap a) where
  foldMap f = foldMap (f . snd) . canonicalFields

instance Traversable (RecordMap a) where
  traverse f = traverseRecordMap (\_ -> f)

-- | The function recordMapAccum threads an accumulating argument through
--   the map in canonical order of fields.
recordMapAccum :: (a -> b -> (a,c)) -> a -> RecordMap k b -> (a, RecordMap k c)
recordMapAccum f z r = (a, r{ recordMap = m' })
  where
  (a, m') = Map.mapAccum f z (recordMap r)

-- | Zip together the fields of two records using the provided action.
--   If some field is present in one record, but not the other,
--   an @Either a a@ will be returned, indicating which record is missing
--   the field, and returning the name of the missing field.
--
--   The @displayOrder@ of the resulting record will be taken from the first
--   argument (rather arbitrarily).
zipRecordsM :: forall t a b c d. (Ord a, Monad t) =>
  (a -> b -> c -> t d) -> RecordMap a b -> RecordMap a c -> t (Either (Either a a) (RecordMap a d))
zipRecordsM f r1 r2 = runExceptT (mkRec <$> zipMap (recordMap r1) (recordMap r2))
  where
  mkRec m = RecordMap m (displayOrder r1)

  zipMap :: Map a b -> Map a c -> ExceptT (Either a a) t (Map a d)
  zipMap = Map.mergeA missingLeft missingRight matched
  missingLeft  = Map.traverseMissing (\a _b -> throwError (Left a))
  missingRight = Map.traverseMissing (\a _c -> throwError (Right a))
  matched = Map.zipWithAMatched (\a b c -> lift (f a b c))

-- | Pure version of `zipRecordsM`
zipRecords :: forall a b c d. Ord a =>
  (a -> b -> c -> d) -> RecordMap a b -> RecordMap a c -> Either (Either a a) (RecordMap a d)
zipRecords f r1 r2 = runIdentity (zipRecordsM (\a b c -> Identity (f a b c)) r1 r2)

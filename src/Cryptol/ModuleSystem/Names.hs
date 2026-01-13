{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BlockArguments #-}
module Cryptol.ModuleSystem.Names where

import Data.Set(Set)
import qualified Data.Set as Set
import Control.DeepSeq(NFData)
import GHC.Generics (Generic)

import Cryptol.Utils.Panic (panic)
import Cryptol.ModuleSystem.Name


-- | A non-empty collection of names used by the renamer.
data Names = One Name | Ambig (Set Name) -- ^ Non-empty
  deriving (Show,Generic,NFData)

-- | The returned list of names will be non-empty.
namesToList :: Names -> [Name]
namesToList xs =
  case xs of
    One x -> [x]
    Ambig ns -> Set.toList ns

anyOne :: Names -> Name
anyOne xs =
  case xs of
    One x -> x
    Ambig ns
      |  Set.null ns
      -> panic "anyOne" ["Ambig with no names"]
      |  otherwise
      -> Set.elemAt 0 ns

anyOneUserName::Names -> Name
anyOneUserName xs = 
    case l of
      [] -> panic "anyOne" ["Ambig with no UserNames"]
      x:_xs -> x
      where 
        l = [ x | x <- namesToList xs, nameSrc x == UserName]

instance Semigroup Names where
  xs <> ys =
    case (xs,ys) of
      (One x, One y)
        | x == y           -> One x
        | otherwise        -> Ambig $! Set.fromList [x,y]
      (One x, Ambig as)    -> Ambig $! Set.insert x as
      (Ambig as, One x)    -> Ambig $! Set.insert x as
      (Ambig as, Ambig bs) -> Ambig $! Set.union as bs

namesFromSet :: Set Name {- ^ Non-empty -} -> Names
namesFromSet xs =
  case Set.minView xs of
    Just (a,ys) -> if Set.null ys then One a else Ambig xs
    Nothing     -> panic "namesFromSet" ["empty set"]

unionManyNames :: [Names] -> Maybe Names
unionManyNames xs =
  case xs of
    [] -> Nothing
    _  -> Just (foldr1 (<>) xs)

mapNames :: (Name -> Name) -> Names -> Names
mapNames f xs =
  case xs of
    One x -> One (f x)
    Ambig as -> namesFromSet (Set.map f as)

filterNames :: (Name -> Bool) -> Names -> Maybe Names
filterNames p names =
  case names of
    One x -> if p x then Just (One x) else Nothing
    Ambig xs -> do let ys = Set.filter p xs
                   (y,zs) <- Set.minView ys
                   if Set.null zs then Just (One y) else Just (Ambig ys)

travNames :: Applicative f => (Name -> f Name) -> Names -> f Names
travNames f xs =
  case xs of
    One x -> One <$> f x
    Ambig as -> namesFromSet . Set.fromList <$> traverse f (Set.toList as)


-- Names that are in the first but not the second
diffNames :: Names -> Names -> Maybe Names
diffNames x y =
  case x of
    One a ->
      case y of
        One b -> if a == b then Nothing
                           else Just (One a)
        Ambig xs -> if a `Set.member` xs then Nothing else Just (One a)
    Ambig xs ->
      do (a,rest) <- Set.minView ys
         pure if Set.null rest then One a else Ambig xs

      where
      ys = case y of
             One z    -> Set.delete z xs
             Ambig zs -> Set.difference xs zs


{-# Language Safe, RankNTypes, MultiParamTypeClasses #-}
{-# Language FunctionalDependencies #-}
{-# Language FlexibleInstances #-}
{-# Language TypeFamilies, UndecidableInstances #-}
{-# Language TypeOperators #-}
module Cryptol.Utils.Patterns where

import Control.Monad(liftM,liftM2,ap,MonadPlus(..),guard)
import qualified Control.Monad.Fail as Fail
import Control.Applicative(Alternative(..))

newtype Match b = Match (forall r. r -> (b -> r) -> r)

instance Functor Match where
  fmap = liftM

instance Applicative Match where
  pure a = Match $ \_no yes -> yes a
  (<*>)  = ap

instance Monad Match where
  Match m >>= f = Match $ \no yes -> m no $ \a ->
                                     let Match n = f a in
                                     n no yes

instance Fail.MonadFail Match where
  fail _ = empty

instance Alternative Match where
  empty = Match $ \no _ -> no
  Match m <|> Match n = Match $ \no yes -> m (n no yes) yes

instance MonadPlus Match where

type Pat a b = a -> Match b


(|||) :: Pat a b -> Pat a b -> Pat a b
p ||| q = \a -> p a <|> q a

-- | Check that a value satisfies multiple patterns.
-- For example, an "as" pattern is @(__ &&& p)@.
(&&&) :: Pat a b -> Pat a c -> Pat a (b,c)
p &&& q = \a -> liftM2 (,) (p a) (q a)

-- | Match a value, and modify the result.
(~>) :: Pat a b -> (b -> c) -> Pat a c
p ~> f = \a -> f <$> p a

-- | Match a value, and return the given result
(~~>) :: Pat a b -> c -> Pat a c
p ~~> f = \a -> f <$ p a

-- | View pattern.
(<~) :: (a -> b) -> Pat b c -> Pat a c
f <~ p = \a -> p (f a)

-- | Variable pattern.
__ :: Pat a a
__ = return

-- | Constant pattern.
succeed :: a -> Pat x a
succeed = const . return

-- | Predicate pattern
checkThat :: (a -> Bool) -> Pat a ()
checkThat p = \a -> guard (p a)

-- | Check for exact value.
lit :: Eq a => a -> Pat a ()
lit x = checkThat (x ==)
{-# Inline lit #-}


-- | Match a pattern, using the given default if valure.
matchDefault :: a -> Match a -> a
matchDefault a (Match m) = m a id
{-# Inline matchDefault #-}

-- | Match an irrefutable pattern.  Crashes on faliure.
match :: Match a -> a
match m = matchDefault (error "Pattern match failure.") m
{-# Inline match #-}

matchMaybe :: Match a -> Maybe a
matchMaybe (Match m) = m Nothing Just


list :: [Pat a b] -> Pat [a] [b]
list [] = \a ->
  case a of
    [] -> return []
    _  -> mzero
list (p : ps) = \as ->
  case as of
    []     -> mzero
    x : xs ->
      do a  <- p x
         bs <- list ps xs
         return (a : bs)


(><) :: Pat a b -> Pat x y -> Pat (a,x) (b,y)
p >< q = \(a,x) -> do b <- p a
                      y <- q x
                      return (b,y)

class Matches thing pats res | pats -> thing res where
  matches :: thing -> pats -> Match res

instance ( f  ~ Pat a a1'
         , a1 ~ Pat a1' r1
         ) => Matches a (f,a1) r1 where
  matches ty (f,a1) = do a1' <- f ty
                         a1 a1'

instance ( op ~ Pat a (a1',a2')
         , a1 ~ Pat a1' r1
         , a2 ~ Pat a2' r2
         ) => Matches a (op,a1,a2) (r1,r2)
  where
  matches ty (f,a1,a2) = do (a1',a2') <- f ty
                            r1 <- a1 a1'
                            r2 <- a2 a2'
                            return (r1,r2)

instance ( op ~ Pat a (a1',a2',a3')
         , a1 ~ Pat a1' r1
         , a2 ~ Pat a2' r2
         , a3 ~ Pat a3' r3
         ) => Matches a (op,a1,a2,a3) (r1,r2,r3) where
  matches ty (f,a1,a2,a3) = do (a1',a2',a3') <- f ty
                               r1 <- a1 a1'
                               r2 <- a2 a2'
                               r3 <- a3 a3'
                               return (r1,r2,r3)




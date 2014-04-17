-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.Lib
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Misc helpers
-----------------------------------------------------------------------------

module Data.SBV.Utils.Lib where

-- | Monadic lift over 2-tuples
mlift2 :: Monad m => (a' -> b' -> r) -> (a -> m a') -> (b -> m b') -> (a, b) -> m r
mlift2 k f g (a, b) = f a >>= \a' -> g b >>= \b' -> return $ k a' b'

-- | Monadic lift over 3-tuples
mlift3 :: Monad m => (a' -> b' -> c' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (a, b, c) -> m r
mlift3 k f g h (a, b, c) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> return $ k a' b' c'

-- | Monadic lift over 4-tuples
mlift4 :: Monad m => (a' -> b' -> c' -> d' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (a, b, c, d) -> m r
mlift4 k f g h i (a, b, c, d) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> return $ k a' b' c' d'

-- | Monadic lift over 5-tuples
mlift5 :: Monad m => (a' -> b' -> c' -> d' -> e' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (a, b, c, d, e) -> m r
mlift5 k f g h i j (a, b, c, d, e) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> return $ k a' b' c' d' e'

-- | Monadic lift over 6-tuples
mlift6 :: Monad m => (a' -> b' -> c' -> d' -> e' -> f' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (f -> m f') -> (a, b, c, d, e, f) -> m r
mlift6 k f g h i j l (a, b, c, d, e, y) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> l y >>= \y' -> return $ k a' b' c' d' e' y'

-- | Monadic lift over 7-tuples
mlift7 :: Monad m => (a' -> b' -> c' -> d' -> e' -> f' -> g' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (f -> m f') -> (g -> m g') -> (a, b, c, d, e, f, g) -> m r
mlift7 k f g h i j l m (a, b, c, d, e, y, z) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> l y >>= \y' -> m z >>= \z' -> return $ k a' b' c' d' e' y' z'

-- | Monadic lift over 8-tuples
mlift8 :: Monad m => (a' -> b' -> c' -> d' -> e' -> f' -> g' -> h' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (f -> m f') -> (g -> m g') -> (h -> m h') -> (a, b, c, d, e, f, g, h) -> m r
mlift8 k f g h i j l m n (a, b, c, d, e, y, z, w) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> l y >>= \y' -> m z >>= \z' -> n w >>= \w' -> return $ k a' b' c' d' e' y' z' w'

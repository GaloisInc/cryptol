{-# LANGUAGE Safe #-}
module Cryptol.Utils.Misc where


{- | Apply the function to all elements in the list.
Return 'Nothing' if all results were 'Nothing', otherwise it
returns @Just answers@, where each @answer@ is either the original
value (if the function gave 'Nothing'), or the result of the function. -}
anyJust :: (a -> Maybe a) -> [a] -> Maybe [a]
anyJust _ []       = Nothing
anyJust f (x : xs) = case (f x, anyJust f xs) of
                       (Nothing, Nothing)   -> Nothing
                       (Just x', Nothing)   -> Just (x' : xs)
                       (Nothing, Just xs')  -> Just (x  : xs')
                       (Just x', Just xs')  -> Just (x' : xs')



{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Safe #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.TypeCheck.SimpType where

import Control.Applicative((<|>))
import Cryptol.TypeCheck.Type hiding
  (tSub,tMul,tDiv,tMod,tExp,tMin,tCeilDiv,tCeilMod,tLenFromThenTo)
import Cryptol.TypeCheck.TypePat
import Cryptol.TypeCheck.Solver.InfNat
import Control.Monad(msum,guard)


tRebuild' :: Bool -> Type -> Type
tRebuild' withUser = go
  where
  go ty =
    case ty of
      TUser x xs t
        | withUser    -> TUser x xs (go t)
        | otherwise   -> go t
      TVar _          -> ty
      TRec xs         -> TRec (fmap go xs)
      TNominal nt xs  -> TNominal nt (map go xs)
      TCon tc ts      -> tCon tc (map go ts)

tRebuild :: Type -> Type
tRebuild = tRebuild' True

tCon :: TCon -> [Type] -> Type
tCon tc ts =
  case tc of
    TF f ->
      case (f, ts) of
        (TCAdd, [x, y]) -> tAdd x y
        (TCSub, [x, y]) -> tSub x y
        (TCMul, [x, y]) -> tMul x y
        (TCExp, [x, y]) -> tExp x y
        (TCDiv, [x, y]) -> tDiv x y
        (TCMod, [x, y]) -> tMod x y
        (TCMin, [x, y]) -> tMin x y
        (TCMax, [x, y]) -> tMax x y
        (TCWidth, [x]) -> tWidth x
        (TCCeilDiv, [x, y]) -> tCeilDiv x y
        (TCCeilMod, [x, y]) -> tCeilMod x y
        (TCLenFromThenTo, [x, y, z]) -> tLenFromThenTo x y z
        _ -> TCon tc ts
    _ -> TCon tc ts

-- Normal: constants to the left
tAdd :: Type -> Type -> Type
tAdd x y
  | Just t <- tOp TCAdd (total (op2 nAdd)) [x,y] = t
  | tIsInf x            = tInf
  | tIsInf y            = tInf
  | Just n <- tIsNum x  = addK n y
  | Just n <- tIsNum y  = addK n x
  | Just (n,x1) <- isSumK x = addK n (tAdd x1 y)
  | Just (n,y1) <- isSumK y = addK n (tAdd x y1)
  | Just v <- matchMaybe (do (a,b) <- (|-|) y
                             guard (x == b)
                             return a) = v
  | Just v <- matchMaybe (do (a,b) <- (|-|) x
                             guard (b == y)
                             return a) = v

  | Just v <- matchMaybe (factor <|> same <|> swapVars) = v

  | otherwise           = tf2 TCAdd x y
  where
  isSumK t = case tNoUser t of
               TCon (TF TCAdd) [ l, r ] ->
                 do n <- tIsNum l
                    return (n, r)
               _ -> Nothing

  addK 0 t = t
  addK n t | Just (m,b) <- isSumK t = tf2 TCAdd (tNum (n + m)) b
           | Just v <- matchMaybe
                     $ do (a,b) <- (|-|) t
                          (do m <- aNat b
                              return $ case compare n m of
                                         GT -> tAdd (tNum (n-m)) a
                                         EQ -> a
                                         LT -> tSub a (tNum (m-n)))
                            <|>
                            (do m <- aNat a
                                return (tSub (tNum (m+n)) b))
                      = v
           -- K + min a b ~> min (K + a) (K + b)
           | Just v <- matchMaybe
                    $ do (a,b) <- aMin t
                         return $ tMin (tAdd (tNum n) a) (tAdd (tNum n) b)
              = v

           | otherwise              = tf2 TCAdd (tNum n) t

  factor = do (a,b1)  <- aMul x
              (a',b2) <- aMul y
              guard (a == a')
              return (tMul a (tAdd b1 b2))

  same = do guard (x == y)
            return (tMul (tNum (2 :: Int)) x)

  swapVars = do a <- aTVar x
                b <- aTVar y
                guard (b < a)
                return (tf2 TCAdd y x)

tSub :: Type -> Type -> Type
tSub x y
  | Just t <- tOp TCSub (op2 nSub) [x,y] = t
  | tIsInf y  = tError (tf2 TCSub x y)

  | tIsInf x = x
    {- This assumes that `y` is finite and not error.  The first should
       follow from the typing on `tSub`, which asserts that the second argument
       is finite and less than the first;  the second should have been handled
       by the first equation above, see `tOp`. -}

  | Just 0 <- yNum = x
  | Just k <- yNum
  , TCon (TF TCAdd) [a,b] <- tNoUser x
  , Just n <- tIsNum a = case compare k n of
                           EQ -> b
                           LT -> tf2 TCAdd (tNum (n - k)) b
                           GT -> tSub b (tNum (k - n))

  | Just v <- matchMaybe (do (a,b) <- anAdd x
                             (guard (a == y) >> return b)
                                <|> (guard (b == y) >> return a))
                       = v

  | Just v <- matchMaybe (do (a,b) <- (|-|) y
                             return (tSub (tAdd x b) a)) = v

  | otherwise = tf2 TCSub x y
  where
  yNum = tIsNum y



-- Normal: constants to the left
tMul :: Type -> Type -> Type
tMul x y
  | Just t <- tOp TCMul (total (op2 nMul)) [x,y] = t
  | Just n <- tIsNum x  = mulK n y
  | Just n <- tIsNum y  = mulK n x
  | Just v <- matchMaybe swapVars = v
  | otherwise = checkExpMul x y
  
  where
  mulK 0 _ = tNum (0 :: Int)
  mulK 1 t = t
  mulK n t | TCon (TF TCMul) [a,b] <- t'
           , Just a' <- tIsNat' a = case a' of
                                     Inf   -> t
                                     Nat m -> tf2 TCMul (tNum (n * m)) b
           | TCon (TF TCDiv) [a,b] <- t'
           , Just b' <- tIsNum b
           -- XXX: similar for a = b * k?
           , n == b' = tSub a (tMod a b)
           -- c * c ^ x = c ^ (1 + x)
           | TCon (TF TCExp) [a,b] <- t'
           , Just n' <- tIsNum a
           , n == n' = tf2 TCExp a (tAdd (tNum (1::Int)) b)
           -- c^x * c^y = c ^ (y + x)
           | otherwise = tf2 TCMul (tNum n) t
    where t' = tNoUser t

  swapVars = do a <- aTVar x
                b <- aTVar y
                guard (b < a)
                return (tf2 TCMul y x)
  
  -- Check if (K^a * K^b) => K^(a + b) otherwise default to standard mul
  checkExpMul s t | TCon (TF TCExp) [a,aExp] <- s
                  , Just a' <- tIsNum a
                  , TCon (TF TCExp) [b,bExp] <- t
                  , Just b' <- tIsNum b
                  , (a' >= 2 && a' == b') = tf2 TCExp a (tAdd aExp bExp)
                  | otherwise = tf2 TCMul x y



tDiv :: Type -> Type -> Type
tDiv x y
  | Just t <- tOp TCDiv (op2 nDiv) [x,y] = t
  | tIsInf x = bad
  | Just 0 <- tIsNum y = bad
  | otherwise = tf2 TCDiv x y
    where bad = tError (tf2 TCDiv x y)

tMod :: Type -> Type -> Type
tMod x y
  | Just t <- tOp TCMod (op2 nMod) [x,y] = t
  | tIsInf x = bad
  | Just 0 <- tIsNum y = bad
  | otherwise = tf2 TCMod x y
    where bad = tError (tf2 TCMod x y)

tCeilDiv :: Type -> Type -> Type
tCeilDiv x y
  | Just t <- tOp TCCeilDiv (op2 nCeilDiv) [x,y] = t
  | tIsInf y = bad
  | Just 0 <- tIsNum y = bad
  | otherwise = tf2 TCCeilDiv x y
    where bad = tError (tf2 TCCeilDiv x y)

tCeilMod :: Type -> Type -> Type
tCeilMod x y
  | Just t <- tOp TCCeilMod (op2 nCeilMod) [x,y] = t
  | tIsInf y = bad
  | Just 0 <- tIsNum x = bad
  | otherwise = tf2 TCCeilMod x y
    where bad = tError (tf2 TCCeilMod x y)


tExp :: Type -> Type -> Type
tExp x y
  | Just t <- tOp TCExp (total (op2 nExp)) [x,y] = t
  | Just 0 <- tIsNum y = tNum (1 :: Int)
  | TCon (TF TCExp) [a,b] <- tNoUser y = tExp x (tMul a b)
  | otherwise = tf2 TCExp x y


-- Normal: constants to the left
tMin :: Type -> Type -> Type
tMin x y
  | Just t <- tOp TCMin (total (op2 nMin)) [x,y] = t
  | Just n <- tIsNat' x = minK n y
  | Just n <- tIsNat' y = minK n x
  | Just n <- matchMaybe (minPlusK x y <|> minPlusK y x) = n
  | Just n <- matchMaybe $ do (k,a) <- isMinK x
                              return $ minK k (tMin a y)
                          <|>
                          do (k,a) <- isMinK y
                             return $ minK k (tMin x a)
    = n

  | Just n <- matchMaybe $ do (k1,a) <- isAddK x
                              (k2,b) <- isAddK y
                              guard (a == b)
                              return $ tAdd (tNum (min k1 k2)) a
    = n

  | x == y              = x
  -- XXX: min (k + t) t -> t
  | otherwise           = tf2 TCMin x y
  where
  isAddK ty = do (a,b) <- anAdd ty
                 k     <- aNat a
                 return (k,b)

  isMinK ty = do (a,b) <- aMin ty
                 k     <- aNat' a
                 return (k,b)

  minPlusK a b = do (k,r) <- isAddK a
                    guard (k >= 1 && b == r)
                    return b


  minK Inf t      = t
  minK (Nat 0) _  = tNum (0 :: Int)
  minK (Nat k) t
    | TCon (TF TCMin) [a,b] <- t'
    , Just n <- tIsNum a   = tf2 TCMin (tNum (min k n)) b

    | otherwise = tf2 TCMin (tNum k) t
    where t' = tNoUser t

-- Normal: constants to the left
tMax :: Type -> Type -> Type
tMax x y
  | Just t <- tOp TCMax (total (op2 nMax)) [x,y] = t
  | Just n <- tIsNat' x = maxK n y
  | Just n <- tIsNat' y = maxK n x
  | otherwise           = tf2 TCMax x y
  where
  maxK Inf _     = tInf
  maxK (Nat 0) t = t
  maxK (Nat k) t

    -- max 1 t ~> t,   if t = a ^ b && a >= 1
    | k == 1
    , TCon (TF TCExp) [a,_] <- t'
    , Just base <- tIsNat' a
    , base >= Nat 1 = t

    | TCon (TF TCAdd) [a,b] <- t'
    , Just n <- tIsNum a = if k <= n
                             then t
                             else tAdd (tNum n) (tMax (tNum (k - n)) b)

    | TCon (TF TCSub) [a,b] <- t'
    , Just n <- tIsNat' a =
      case n of
        Inf   -> t
        Nat m -> if k >= m then tNum k else tSub a (tMin (tNum (m - k)) b)

    | TCon (TF TCMax) [a,b] <- t'
    , Just n <- tIsNum a  = tf2 TCMax (tNum (max k n)) b

    | otherwise = tf2 TCMax (tNum k) t
    where t' = tNoUser t


tWidth :: Type -> Type
tWidth x
  | Just t <- tOp TCWidth (total (op1 nWidth)) [x] = t

  -- width (2^n - 1) = n
  | TCon (TF TCSub) [a,b] <- tNoUser x
  , Just 1 <- tIsNum b
  , TCon (TF TCExp) [p,q] <- tNoUser a
  , Just 2 <- tIsNum p = q

  | otherwise = tf1 TCWidth x

tLenFromThenTo :: Type -> Type -> Type -> Type
tLenFromThenTo x y z
  | Just t <- tOp TCLenFromThenTo (op3 nLenFromThenTo) [x,y,z] = t
  | otherwise = tf3 TCLenFromThenTo x y z

total :: ([Nat'] -> Nat') -> ([Nat'] -> Maybe Nat')
total f xs = Just (f xs)

op1 :: (a -> b) -> [a] -> b
op1 f ~[x] = f x

op2 :: (a -> a -> b) -> [a] -> b
op2 f ~[x,y] = f x y

op3 :: (a -> a -> a -> b) -> [a] -> b
op3 f ~[x,y,z] = f x y z

-- | Common checks: check for error, or simple full evaluation.
-- We assume that input kinds and the result kind are the same (i.e., Nat)
tOp :: TFun -> ([Nat'] -> Maybe Nat') -> [Type] -> Maybe Type
tOp tf f ts
  | Just t <- msum (map tIsError ts) = Just (tError t)
    -- assumes result kind the same as input kind

  | Just xs <- mapM tIsNat' ts =
      Just $ case f xs of
               Nothing -> tError (TCon (TF tf) (map tNat' xs))
               Just n  -> tNat' n
  | otherwise = Nothing





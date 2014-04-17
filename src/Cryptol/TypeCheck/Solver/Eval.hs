-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- We define the behavior of Cryptol's type-level functions on
-- integers.

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.Eval where

import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.TypeCheck.Solver.FinOrd
import           Cryptol.TypeCheck.Solver.Interval
import           Cryptol.TypeCheck.Solver.Utils(splitConstSummand)

import           Data.List(sortBy)

--------------------------------------------------------------------------------
-- Simplify a type
-- NOTE: These functions assume zonked types.

{- DO THIS
-- XXX
reAssocArgs :: OrdFacts -> TFun -> [Type] -> [Type]
reAssocArgs info TCAdd [ t1, TCon (TF TCAdd) [t2, t3]]
  | Just t4 <- tfAdd info t1 t2  = reAssocArgs info TCAdd [t4,t3]

reAssocArgs _ TCAdd [ TCon (TF TCAdd) [t1, t2], t3] = [ t1, t2 .+. t3 ]

reAssocArgs info TCMul [ t1, TCon (TF TCMul) [t2, t3]]
  | Just t4 <- tfMul info t1 t2   = reAssocArgs info TMul [t4, t3]

reAssocArgs _ TCMul [ TCon (TF TCMul) [t1, t2], t3] = [ t1, t2 .*. t3 ]

reAssocArgs _ _ ts = ts
-}

--------------------------------------------------------------------------------

{- | Collect `fin` and simple `<=` constraints in the ord model
Returns `Left` if we find a goal which is incompatible with the others.
Otherwise, we return `Right` with a model, and the remaining
(i.e., the non-order related) properties.

These sorts of facts are quite useful during type simplification, because
they provide information which potentially useful for cancellation
(e.g., this variables is finite and not 0)
-}
assumedOrderModel :: OrdFacts -> [Prop] ->
                        Either (OrdFacts,Prop) (OrdFacts, [Prop])

assumedOrderModel m0 todo = go m0 [] False (map (simpType m0) todo)
  where
  go m others changes []
    | changes   = assumedOrderModel m others
    | otherwise =
      case concatMap (derivedOrd m) others of
        []      -> Right (m, others)
        derived -> case assumedOrderModel m derived of
                     Left err -> Left err
                     Right (m1,os) -> Right (m1,os++others)

  go m others changes (g : gs) =
    case addFact g m of
      OrdAlreadyKnown   -> go m  others changes gs
      OrdAdded m1       -> go m1 others True gs
      OrdCannot         -> go m (g : others) changes gs
      OrdImprove t1 t2  -> go m ((t1 =#= t2) : others) changes gs
      OrdImpossible     -> Left (m,g)


-- | This returns order properties that are implied by the give property.
-- It is important that the returned properties are propoer ordering 
-- properties (i.e., `addFact` will not return `OrdCannot`).
derivedOrd :: OrdFacts -> Prop -> [Prop]
derivedOrd m prop =
  case prop of
    TUser _ _ p -> derivedOrd m p

    TCon (PC PGeq) [TVar x, t2] | notSimple t2 -> lowerCt x (typeInterval m t2)
    TCon (PC PGeq) [t1,TVar x] | notSimple t1  -> upperCt x (typeInterval m t1)
    TCon (PC PEqual) [TVar x, t]
      | notSimple t -> equalCt x (typeInterval m t)
    TCon (PC PEqual) [t, TVar x]
      | notSimple  t -> equalCt x (typeInterval m t)
    _ -> []

  where
  notSimple = not . isSimpleType
  equalCt x i = lowerCt x i ++ upperCt x i
  lowerCt x i = [ TVar x >== fromNat' (lowerBound i) ]
  upperCt x i = case upperBound i of
                  Nat n -> [ tNum n >== TVar x ]
                  Inf | isFinite i -> [ pFin (TVar x) ]
                      | otherwise  -> []

isSimpleType :: Type -> Bool
isSimpleType (TCon (TC TCInf) _)      = True
isSimpleType (TCon (TC (TCNum _)) _)  = True
isSimpleType (TVar _)                 = True
isSimpleType _                        = False


--------------------------------------------------------------------------------


-- Performs only forward evaluation.
simpType :: OrdFacts -> Type -> Type
simpType i ty =
  case ty of
    TUser f ts t   -> TUser f (map (simpType i) ts) (simpType i t)
    TCon (TF f) ts -> let ts1 = reorderArgs f (map (simpType i) ts)
                      in case evalTFun i f ts1 of
                           Nothing -> TCon (TF f) ts1
                           Just t1 -> simpType i t1
    TCon tc ts     -> TCon tc (map (simpType i) ts)
    TRec fs        -> TRec [ (l,simpType i t) | (l,t) <- fs ]
    _              -> ty

reorderArgs :: TFun -> [Type] -> [Type]
reorderArgs TCAdd ts = commuteArgs ts
reorderArgs TCMul ts = commuteArgs ts
reorderArgs _ ts     = ts

-- Move constants to the front, followed by free variables, followed by
-- bound variables, followed by other expressions.
commuteArgs :: [Type] -> [Type]
commuteArgs = sortBy cmp
  where
  cmp (TCon (TC (TCNum x)) _) (TCon (TC (TCNum y)) _) = compare x y
  cmp (TCon (TC (TCNum _)) _) _                       = LT
  cmp _                       (TCon (TC (TCNum _)) _) = GT

  cmp (TCon (TC TCInf) _) (TCon (TC TCInf) _) = EQ
  cmp (TCon (TC TCInf) _) _                   = LT
  cmp _                   (TCon (TC TCInf) _) = GT

  cmp (TVar x) (TVar y)   = compare x y
  cmp (TVar _) _          = LT
  cmp _         (TVar _)  = GT

  cmp _ _                 = EQ


evalTFun :: OrdFacts -> TFun -> [Type] -> Maybe Type
evalTFun i tfun args =
  case (tfun, args) of
    (TCAdd, [t1,t2])             -> tfAdd i t1 t2
    (TCSub, [t1,t2])             -> tfSub i t1 t2
    (TCMul, [t1,t2])             -> tfMul i t1 t2
    (TCDiv, [t1,t2])             -> tfDiv i t1 t2
    (TCMod, [t1,t2])             -> tfMod i t1 t2
    (TCExp, [t1,t2])             -> tfExp i t1 t2
    (TCMin, [t1,t2])             -> tfMin i t1 t2
    (TCMax, [t1,t2])             -> tfMax i t1 t2
    (TCLg2, [t1])                -> tfLg2 i t1
    (TCWidth, [t1])              -> tfWidth i t1
    (TCLenFromThen,  [t1,t2,t3]) -> tfLenFromThen   i t1 t2 t3
    (TCLenFromThenTo,[t1,t2,t3]) -> tfLenFromThenTo i t1 t2 t3

    _                            -> Nothing




typeInterval :: OrdFacts -> Type -> Interval
typeInterval i = go . simpType i
  where
  go ty =
    case ty of
      TVar {}     -> knownInterval i ty
      TUser _ _ t -> go t
      TCon (TC (TCNum x)) _ -> iConst (Nat x)
      TCon (TF f) ts ->
        case (f,ts) of
          (TCAdd,   [t1,t2]) -> iAdd (go t1) (go t2)
          (TCSub,   [t1,t2]) -> iSub (go t1) (go t2)
          (TCMul,   [t1,t2]) -> iMul (go t1) (go t2)
          (TCDiv,   [t1,t2]) -> iDiv (go t1) (go t2)
          (TCMod,   [t1,t2]) -> iMod (go t1) (go t2)
          (TCExp,   [t1,t2]) -> iExp (go t1) (go t2)
          (TCLg2,   [t1])    -> iLg2 (go t1)
          (TCWidth, [t1])    -> iWidth (go t1)

          (TCLenFromThen,  [t1,t2,t3]) -> iLenFromThen   (go t1) (go t2) (go t3)
          (TCLenFromThenTo,[t1,t2,t3]) -> iLenFromThenTo (go t1) (go t2) (go t3)

          _                  -> anything
      _ -> anything

typeKnownLeq :: OrdFacts -> Type -> Type -> Bool
typeKnownLeq _ _ (TCon (TC TCInf) _)     = True
typeKnownLeq _ (TCon (TC (TCNum 0)) _) _ = True

typeKnownLeq _ t1 t2 | t1 == t2          = True

typeKnownLeq m t1 t2 | upperBound i1 <= lowerBound i2  = True
  where i1 = typeInterval m t1
        i2 = typeInterval m t2

typeKnownLeq _ t1 t2
  | Just (_,t2') <- splitConstSummand t2, t1 == t2' = True

typeKnownLeq m t1 t2 = isKnownLeq m t1 t2

typeKnownFin :: OrdFacts -> Type -> Bool
typeKnownFin m t = isFinite (typeInterval m t)



--------------------------------------------------------------------------------

tfAdd :: OrdFacts -> Type -> Type -> Maybe Type
tfAdd m t1 t2
  | Just Inf      <- arg1 = Just tInf

  | Just (Nat 0)  <- arg1 = Just t2

  | Just Inf      <- arg2 = Just tInf

  | Just (Nat 0)  <- arg2 = Just t1

  | Just (Nat x)  <- arg1
  , Just (Nat y)  <- arg2 = Just $ tNum $ x + y

  -- k1 + (k2 + t)  = (k1 + k1) + t
  | Just (Nat k1) <- arg1
  , TCon (TF TCAdd) [ s1, s2 ] <- tNoUser t2
  , Just (Nat k2) <- toNat' s1  = Just $ tNum (k1 + k2) .+. s2

  -- Simplification for `k1 + (t - k2)`
  -- This is only OK as long as we know that `t - k2` is well-defined.
  | Just (Nat x)               <- arg1
  , TCon (TF TCSub) [ s1, s2 ] <- t2
  , Just (Nat y)               <- toNat' s2
  , let i = lowerBound (typeInterval m s1)
  , i >= Nat y            = Just (if x >= y then tNum (x - y) .+. s1
                                            else s1 .-. tNum (y - x))

  -- a + a = 2 * a
  | t1 == t2              = Just (tNum (2 :: Int) .*. t1)

  -- k * a + a = (k + 1) * a
  | TCon (TF TCMul) [s1,s2] <- tNoUser t1
  , Just x <- toNat' s1
  , s2 == t2              = factorConst x (Nat 1) t2

  -- a + k * a = (k + 1) * a
  | TCon (TF TCMul) [s1,s2] <- tNoUser t2
  , Just x <- toNat' s1
  , s2 == t1              = factorConst x (Nat 1) t1

  -- k1 * a + k2 * a = (k1 + k1) * a
  | TCon (TF TCMul) [s1,s2] <- tNoUser t1
  , Just x <- toNat' s1
  , TCon (TF TCMul) [p1,p2] <- tNoUser t2
  , Just y <- toNat' p1
  , s2 == p2              = factorConst x y p1


  | otherwise             = Nothing

  where arg1 = toNat' t1
        arg2 = toNat' t2

        factorConst k1 k2 t = Just $ fromNat' (nAdd k1 k2) .*. t



{- | @tfSub x y = Just z@ iff @z@ is the unique value such that 
@tfAdd y z = Just x@ -}
tfSub :: OrdFacts -> Type -> Type -> Maybe Type
tfSub i t1 t2
  | Just (Nat 0) <- arg2  = Just t1

  | Just Inf <- arg1
  , typeKnownFin i t2       = Just tInf

  -- k1 - k2
  | Just (Nat x) <- arg1
  , Just (Nat y) <- arg2
  , x >= y                = Just $ tNum (x - y)

  -- (x - y) - z  = x - (y + z)
  | TCon (TF TCSub) [s1,s2] <- t1 = Just (s1 .-. (s2 .+. t2))

  -- (k1 + t) - k2
  | TCon (TF TCAdd) [s1,s2] <- t1
  , Just k1 <- toNat' s1
  , Just k2 <- arg2   = case (nSub k1 k2, nSub k2 k1) of

                          -- = (k1 - k2) + t
                          (Just a, _) -> Just (fromNat' a .+. s2)

                          -- = t - (k2 - k1)
                          (_, Just a) -> Just (s2 .-. fromNat' a)

                          _ -> Nothing

  | otherwise             = Nothing


  where arg1 = toNat' t1
        arg2 = toNat' t2


-- | It is important that the 0 rules come before the `Inf` ones
tfMul :: OrdFacts -> Type -> Type -> Maybe Type
tfMul i t1 t2
  | Just (Nat 0) <- arg1  = Just t1


  | Just (Nat 1) <- arg1  = Just t2

  | Just (Nat 0) <- arg2  = Just t2

  | Just (Nat 1) <- arg2  = Just t1

  | Just Inf     <- arg1
  , oneOrMore i t2        = Just tInf

  | Just Inf     <- arg2
  , oneOrMore i t1        = Just tInf

  | Just (Nat x) <- arg1
  , Just (Nat y) <- arg2  = Just $ tNum $ x * y

  -- k1 * (k2 * t)  = (k1 * k2) * t
  | Just k1 <- arg1
  , TCon (TF TCMul) [s1,s2] <- t2
  , Just k2 <- toNat' s1  = Just $ fromNat' (nMul k1 k2) .*. s2

  | otherwise             = Nothing

  where arg1 = toNat' t1
        arg2 = toNat' t2

{- y * q + r = x
x / y = q with remainder r
0 <= r && r < y -}
tfDiv :: OrdFacts -> Type -> Type -> Maybe Type
tfDiv i t1 t2
  | Just (Nat 1) <- arg2      = Just t1

  | Just Inf     <- arg2
  , typeKnownFin i t1           = Just $ tNum (0 :: Int)

  | Just (Nat 0) <- arg1
  , Nat 1 <= lowerBound iT2   = Just $ tNum (0 :: Int)

  | Just Inf <- arg1
  , Nat 1 <= lowerBound iT2 &&
    isFinite iT2              = Just tInf

  | Just (Nat x) <- arg1
  , Just (Nat y) <- arg2
  , 1 <= y                   = Just $ tNum $ div x y

  -- (k1 * t) / k2  = (k1/k2) * t   , as long as the division is exact
  | TCon (TF TCMul) [ s1, s2 ] <- tNoUser t1
  , Just k1  <- toNat' s1
  , Just k2  <- arg2
  , Just res <- nDiv k1 k2    = Just $ fromNat' res .*. s2

  | otherwise                 = Nothing

  where arg1 = toNat' t1
        arg2 = toNat' t2

        iT2  = knownInterval i t2


tfMod :: OrdFacts -> Type -> Type -> Maybe Type
tfMod i t1 t2
  | Just (Nat 1) <- arg2    = Just $ tNum (0 :: Int)

  | Just Inf     <- arg2
  , typeKnownFin i t1         = Just t1

  | Just (Nat 0) <- arg1
  , Nat 1 <= lowerBound iT2 = Just $ tNum (0 :: Int)

  -- There is no unique remainder in the case when we are dividing
  -- @Inf@ by a natural number.

  | Just (Nat x) <- arg1
  , Just (Nat y) <- arg2
  , 1 <= y                  = Just $ tNum $ mod x y

  | otherwise               = Nothing

  where arg1 = toNat' t1
        arg2 = toNat' t2

        iT2  = knownInterval i t2




tfMin :: OrdFacts -> Type -> Type -> Maybe Type
tfMin i t1 t2
  | typeKnownLeq i t1 t2  = Just t1
  | typeKnownLeq i t2 t1  = Just t2
  | otherwise           = Nothing

tfMax :: OrdFacts -> Type -> Type -> Maybe Type
tfMax i t1 t2
  | typeKnownLeq i t1 t2  = Just t2
  | typeKnownLeq i t2 t1  = Just t1
  | otherwise           = Nothing


-- x ^ 0        = 1
-- x ^ (n + 1)  = x * (x ^ n)
-- x ^ (m + n)  = (x ^ m) * (x ^ n)
-- x ^ (m * n)  = (x ^ m) ^ n
tfExp :: OrdFacts -> Type -> Type -> Maybe Type
tfExp i t1 t2
  | Just (Nat 0) <- arg1
  , oneOrMore i t2            = Just $ tNum (0 :: Int)

  | Just (Nat 1) <- arg1      = Just $ tNum (1 :: Int)

  | Just Inf <- arg1
  , oneOrMore i t2            = Just tInf

  | Just (Nat 0) <- arg2      = Just $ tNum (1 :: Int)

  | Just (Nat 1) <- arg2      = Just t1

  | Just Inf <- arg2
  , twoOrMore i t1            = Just tInf

  | Just (Nat x) <- arg1
  , Just (Nat y) <- arg2      = Just $ tNum $ x ^ y

  | otherwise                 = Nothing

  where arg1 = toNat' t1
        arg2 = toNat' t2


-- | Rounds up
-- @lg2 x = Just y@, if @y@ is the smallest number such that @x <= 2 ^ y@
tfLg2 :: OrdFacts -> Type -> Maybe Type
tfLg2 _ t
  | Just (Nat 0) <- arg     = Just $ tNum (0 :: Int)  -- XXX: should this be defined?
  | Just (Nat x) <- arg     = do (n,exact) <- genLog x 2
                                 return $ tNum $ if exact then n else n + 1
  | Just Inf     <- arg     = Just tInf
  | otherwise               = Nothing

  where arg = toNat' t

-- | XXX: @width@ and @lg2@ are almost the same!
-- @width n == lg2 (n + 1)@
tfWidth :: OrdFacts -> Type -> Maybe Type

-- width (2 ^ a - 1) = a
tfWidth _ ty
  | TCon (TF TCSub) [ t1, TCon (TC (TCNum 1)) _ ] <- ty
  , TCon (TF TCExp) [ TCon (TC (TCNum 2)) _, t2 ] <- t1 = Just t2

tfWidth _ t
  | Just (Nat 0)   <- arg = return $ tNum (0 :: Int)
  | Just (Nat x)   <- arg = do (n,_) <- genLog x 2
                               return $ tNum $ n + 1
  | Just Inf <- arg       = Just tInf
  | otherwise             = Nothing

  where arg = toNat' t

-- len [ t1, t2 .. ] : [_][t3]
tfLenFromThen :: OrdFacts -> Type -> Type -> Type -> Maybe Type
tfLenFromThen i t1 t2 t3

  -- (t2 >= t1) => len [ t1, t2 .. ] = len [ t1, t2, .. 0 ]
  | typeKnownLeq i t2 t1        = tfLenFromThenTo i t1 t2 (tNum (0 :: Int))

  | Just x <- arg1
  , Just y <- arg2
  , Just z <- arg3              = fmap fromNat' (nLenFromThen x y z)

  | otherwise                   = Nothing

  where
  arg1 = toNat' t1
  arg2 = toNat' t2
  arg3 = toNat' t3

tfLenFromThenTo :: OrdFacts -> Type -> Type -> Type -> Maybe Type
tfLenFromThenTo _ t1 t2 t3
  | Just x <- toNat' t1
  , Just y <- toNat' t2
  , Just z <- toNat' t3       = fmap fromNat' (nLenFromThenTo x y z)

  | otherwise = Nothing





--------------------------------------------------------------------------------

toNat' :: Type -> Maybe Nat'
toNat' ty =
  case ty of
    TUser _ _ t           -> toNat' t
    TCon (TC TCInf) _     -> Just Inf
    TCon (TC (TCNum x)) _ -> Just (Nat x)
    _                     -> Nothing

fromNat' :: Nat' -> Type
fromNat' Inf = tInf
fromNat' (Nat x) = tNum x

oneOrMore :: OrdFacts -> Type -> Bool
oneOrMore i t = typeKnownLeq i (tNum (1::Int)) t

twoOrMore :: OrdFacts -> Type -> Bool
twoOrMore i t = typeKnownLeq i (tNum (2::Int)) t





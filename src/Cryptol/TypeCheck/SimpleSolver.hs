{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.SimpleSolver
  ( simplify
  , simplifyStep
  , tAdd, tSub, tMul, tDiv, tMod, tExp
  , tMin, tMax, tWidth, tLenFromThen, tLenFromThenTo
  ) where

import Data.Map(Map)
import Control.Monad(msum)

import Cryptol.TypeCheck.Type hiding
  ( tAdd, tSub, tMul, tDiv, tMod, tExp, tMin, tMax, tWidth
  , tLenFromThen, tLenFromThenTo)
import Cryptol.TypeCheck.PP(pp)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Fin(cryIsFinType)
import Cryptol.TypeCheck.Solver.Numeric.Interval(Interval)
import Cryptol.TypeCheck.Solver.Numeric(cryIsEqual, cryIsNotEqual, cryIsGeq)
import Cryptol.TypeCheck.Solver.Class(solveArithInst,solveCmpInst)

type Ctxt = Map TVar Interval


simplify :: Ctxt -> Prop -> Prop
simplify ctxt p =
  case simplifyStep ctxt p of
    Unsolvable e -> pError e
    Unsolved     -> p
    SolvedIf ps  -> pAnd (map (simplify ctxt) ps)


simplifyStep :: Ctxt -> Prop -> Solved
simplifyStep ctxt prop =
  case tNoUser prop of
    TCon (PC PTrue)  []       -> SolvedIf []
    TCon (PC PAnd)   [l,r]    -> SolvedIf [l,r]

    TCon (PC PArith) [ty]     -> solveArithInst ty
    TCon (PC PCmp)   [ty]     -> solveCmpInst   ty

    TCon (PC PFin)   [ty]     -> cryIsFinType ctxt ty

    TCon (PC PEqual) [t1,t2]  -> cryIsEqual ctxt t1 t2
    TCon (PC PNeq)  [t1,t2]   -> cryIsNotEqual ctxt t1 t2
    TCon (PC PGeq)  [t1,t2]   -> cryIsGeq ctxt t1 t2

    _                         -> Unsolved




--------------------------------------------------------------------------------
-- Construction of type functions

-- Normal: constants to the left
tAdd :: Type -> Type -> Type
tAdd x y
  | Just t <- tOp TCAdd (total (op2 nAdd)) [x,y] = t
  | tIsInf x            = tInf
  | tIsInf y            = tInf
  | Just n <- tIsNum x  = addK n y
  | Just n <- tIsNum y  = addK n x
  | otherwise           = tf2 TCAdd x y
  where
  addK 0 t = t
  addK n t | TCon (TF TCAdd) [a,b] <- tNoUser t
           , Just m <- tIsNum a = tf2 TCAdd (tNum (n + m)) b
           | otherwise          = tf2 TCAdd (tNum n) t

tSub :: Type -> Type -> Type
tSub x y
  | Just t <- tOp TCSub (op2 nSub) [x,y] = t
  | tIsInf y  = tBadNumber $ TCErrorMessage "Subtraction of `inf`."
  | Just 0 <- yNum = x
  | Just k <- yNum
  , TCon (TF TCAdd) [a,b] <- tNoUser x
  , Just n <- tIsNum a = case compare k n of
                           EQ -> b
                           LT -> tf2 TCAdd (tNum (n - k)) b
                           GT -> tSub b (tNum (k - n))
  | otherwise = tf2 TCSub x y
  where
  yNum = tIsNum y



-- Normal: constants to the left
tMul :: Type -> Type -> Type
tMul x y
  | Just t <- tOp TCMul (total (op2 nMul)) [x,y] = t
  | Just n <- tIsNum x  = mulK n y
  | Just n <- tIsNum y  = mulK n x
  | otherwise           = tf2 TCMul x y
  where
  mulK 0 _ = tNum (0 :: Int)
  mulK 1 t = t
  mulK n t | TCon (TF TCMul) [a,b] <- tNoUser t
           , Just a' <- tIsNat' a = case a' of
                                     Inf   -> t
                                     Nat m -> tf2 TCMul (tNum (n * m)) b
           | otherwise = tf2 TCMul (tNum n) t

tDiv :: Type -> Type -> Type
tDiv x y
  | Just t <- tOp TCDiv (op2 nDiv) [x,y] = t
  | tIsInf x = tBadNumber $ TCErrorMessage "Division of `inf`."
  | Just 0 <- tIsNum y = tBadNumber $ TCErrorMessage "Division by 0."
  | otherwise = tf2 TCDiv x y


tMod :: Type -> Type -> Type
tMod x y
  | Just t <- tOp TCMod (op2 nMod) [x,y] = t
  | tIsInf x = tBadNumber $ TCErrorMessage "Modulus of `inf`."
  | Just 0 <- tIsNum x = tBadNumber $ TCErrorMessage "Modulus by 0."
  | otherwise = tf2 TCMod x y

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
  -- XXX: min (k + t) t
  | otherwise           = tf2 TCMin x y
  where
  minK Inf t      = t
  minK (Nat 0) _  = tNum (0 :: Int)
  minK (Nat k) t
    | TCon (TF TCAdd) [a,b] <- t'
    , Just n <- tIsNum a   = if k <= n then tNum k
                                       else tAdd a (tMin (tNum (k - n)) b)

    | TCon (TF TCSub) [a,b] <- t'
    , Just n <- tIsNum a =
      if k >= n then t else tSub a (tMax (tNum (n - k)) b)

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

    | TCon (TF TCAdd) [a,b] <- t'
    , Just n <- tIsNum a = if k <= n
                             then t
                             else tMax (tNum (k - n)) b

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
  | otherwise = tf1 TCWidth x

tLenFromThen :: Type -> Type -> Type -> Type
tLenFromThen x y z
  | Just t <- tOp TCLenFromThen (op3 nLenFromThen) [x,y,z] = t
  -- XXX: rules?
  | otherwise = tf3 TCLenFromThen x y z

tLenFromThenTo :: Type -> Type -> Type -> Type
tLenFromThenTo x y z
  | Just t <- tOp TCLenFromThen (op3 nLenFromThen) [x,y,z] = t
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
tOp :: TFun -> ([Nat'] -> Maybe Nat') -> [Type] -> Maybe Type
tOp tf f ts
  | Just e  <- msum (map tIsError ts) = Just (tBadNumber e)
  | Just xs <- mapM tIsNat' ts =
      Just $ case f xs of
               Nothing -> tBadNumber (err xs)
               Just n  -> tNat' n
  | otherwise = Nothing
  where
  err xs = TCErrorMessage $
              "Invalid applicatoin of " ++ show (pp tf) ++ " to " ++
                  unwords (map show xs)






{-# LANGUAGE Safe, PatternGuards, MultiWayIf #-}
module Cryptol.TypeCheck.Solver.Numeric
  ( cryIsEqual, cryIsNotEqual, cryIsGeq
  ) where

import           Control.Applicative(Alternative(..))
import           Control.Monad (guard,mzero)

import Cryptol.Utils.Patterns
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.TypePat
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Interval
import Cryptol.TypeCheck.SimpType


cryIsEqual :: Ctxt -> Type -> Type -> Solved
cryIsEqual ctxt t1 t2 =
  matchDefault Unsolved $
        (pBin PEqual (==) t1 t2)
    <|> (aNat' t1 >>= tryEqK ctxt t2)
    <|> (aNat' t2 >>= tryEqK ctxt t1)
    <|> (aTVar t1 >>= tryEqVar t2)
    <|> (aTVar t2 >>= tryEqVar t1)
    <|> ( guard (t1 == t2) >> return (SolvedIf []))
    <|> tryEqMin t1 t2
    <|> tryEqMin t2 t1



cryIsNotEqual :: Ctxt -> Type -> Type -> Solved
cryIsNotEqual _i t1 t2 = matchDefault Unsolved (pBin PNeq (/=) t1 t2)

cryIsGeq :: Ctxt -> Type -> Type -> Solved
cryIsGeq i t1 t2 =
  matchDefault Unsolved $
        (pBin PGeq (>=) t1 t2)
    <|> (aNat' t1 >>= tryGeqKThan i t2)
    <|> (aNat' t2 >>= tryGeqThanK i t1)
    <|> (aTVar t2 >>= tryGeqThanVar i t1)
    <|> tryGeqThanSub i t1 t2
    <|> (geqByInterval i t1 t2)
    <|> (guard (t1 == t2) >> return (SolvedIf []))


  -- XXX: max a 10 >= 2 --> True
  -- XXX: max a 2 >= 10 --> a >= 10


pBin :: PC -> (Nat' -> Nat' -> Bool) -> Type -> Type -> Match Solved
pBin tf p t1 t2 =
      Unsolvable <$> anError t1
  <|> Unsolvable <$> anError t2
  <|> (do x <- aNat' t1
          y <- aNat' t2
          return $ if p x y
                      then SolvedIf []
                      else Unsolvable $ TCErrorMessage
                        $ "Predicate " ++ show (pp tf) ++ " does not hold for "
                              ++ show x ++ " and " ++ show y)


--------------------------------------------------------------------------------
-- GEQ

tryGeqKThan :: Ctxt -> Type -> Nat' -> Match Solved
tryGeqKThan _ _ Inf = return (SolvedIf [])
tryGeqKThan _ ty (Nat n) =
  do (a,b) <- aMul ty
     m     <- aNat' a
     return $ SolvedIf
            $ case m of
                Inf   -> [ b =#= tZero ]
                Nat 0 -> []
                Nat k -> [ tNum (div n k) >== b ]

tryGeqThanK :: Ctxt -> Type -> Nat' -> Match Solved
tryGeqThanK _ t Inf = return (SolvedIf [ t =#= tInf ])
tryGeqThanK _ t (Nat k) =
  do (a,b) <- anAdd t
     n     <- aNat a
     return $ SolvedIf $ if n >= k
                            then []
                            else [ b >== tNum (k - n) ]



tryGeqThanSub :: Ctxt -> Type -> Type -> Match Solved
tryGeqThanSub _ x y =
  do (a,_) <- (|-|) y
     guard (x == a)
     return (SolvedIf [])

tryGeqThanVar :: Ctxt -> Type -> TVar -> Match Solved
tryGeqThanVar _ctxt ty x =
  do (a,b) <- anAdd ty
     let check y = do x' <- aTVar y
                      guard (x == x')
                      return (SolvedIf [])
     check a <|> check b

geqByInterval :: Ctxt -> Type -> Type -> Match Solved
geqByInterval ctxt x y =
  let ix = typeInterval ctxt x
      iy = typeInterval ctxt y
  in case (iLower ix, iUpper iy) of
       (l,Just n) | l >= n -> return (SolvedIf [])
       _                   -> mzero

--------------------------------------------------------------------------------


tryEqMin :: Type -> Type -> Match Solved
tryEqMin x y =
  do (a,b) <- aMin x
     let check m1 m2 = do guard (m1 == y)
                          return $ SolvedIf [ m2 >== m1 ]
     check a b <|> check b a


tryEqVar :: Type -> TVar -> Match Solved
tryEqVar ty x =

  -- x = K + x --> x = inf
  (do (k,tv) <- matches ty (anAdd, aNat, aTVar)
      guard (tv == x && k >= 1)

      return $ SolvedIf [ TVar x =#= tInf ]
  )
  <|>

  -- x = min (K + x) y --> x = y
  (do (l,r) <- aMin ty
      let check this other =
            do (k,x') <- matches this (anAdd, aNat', aTVar)
               guard (x == x' && k >= Nat 1)
               return $ SolvedIf [ TVar x =#= other ]
      check l r <|> check r l
  )
  <|>
  -- x = K + min a x
  (do (k,(l,r)) <- matches ty (anAdd, aNat, aMin)
      guard (k >= 1)
      let check a b = do x' <- aTVar a
                         guard (x' == x)
                         return (SolvedIf [ TVar x =#= tAdd (tNum k) b ])
      check l r <|> check r l
  )







-- e.g., 10 = t
tryEqK :: Ctxt -> Type -> Nat' -> Match Solved
tryEqK ctxt ty lk =
  do guard (lk == Inf)
     (a,b) <- anAdd ty
     let check x y = do guard (iIsFin (typeInterval ctxt x))
                        return $ SolvedIf [ y =#= tInf ]
     check a b <|> check b a
  <|>
  do (rk, b) <- matches ty (anAdd, aNat', __)
     return $
       case nSub lk rk of
         -- NOTE: (Inf - Inf) shouldn't be possible
         Nothing -> Unsolvable
                      $ TCErrorMessage
                      $ "Adding " ++ show rk ++ " will always exceed "
                                  ++ show lk

         Just r -> SolvedIf [ b =#= tNat' r ]
  <|>
  do (rk, b) <- matches ty (aMul, aNat', __)
     return $
       case (lk,rk) of
         (Inf,Inf)    -> SolvedIf [ b >== tOne ]
         (Inf,Nat _)  -> SolvedIf [ b =#= tInf ]
         (Nat 0, Inf) -> SolvedIf [ b =#= tZero ]
         (Nat k, Inf) -> Unsolvable
                       $ TCErrorMessage
                       $ show k ++ " /= inf * anything"
         (Nat lk', Nat rk')
           | rk' == 0 -> SolvedIf [ tNat' lk =#= tZero ]
              -- shouldn't happen, as `0 * x = x`
           | (q,0) <- divMod lk' rk' -> SolvedIf [ b =#= tNum q ]
           | otherwise ->
               Unsolvable
             $ TCErrorMessage
             $ show lk ++ " /= " ++ show rk ++ " * anything"

  -- XXX: Min, Max, etx
  -- 2  = min (10,y)  --> y = 2
  -- 2  = min (2,y)   --> y >= 2
  -- 10 = min (2,y)   --> impossible





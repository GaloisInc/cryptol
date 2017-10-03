{-# LANGUAGE Safe, PatternGuards, MultiWayIf #-}
module Cryptol.TypeCheck.Solver.Numeric
  ( cryIsEqual, cryIsNotEqual, cryIsGeq
  ) where

import           Control.Applicative(Alternative(..))
import           Control.Monad (guard,mzero)
import           Data.Foldable (asum)

import Cryptol.Utils.Patterns
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type hiding (tMul)
import Cryptol.TypeCheck.TypePat
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Interval
import Cryptol.TypeCheck.SimpType

{- Convention for comments:

  K1, K2 ...          Concrete constants
  s1, s2, t1, t2 ...  Arbitrary type expressions
  a, b, c ...         Type variables

-}


-- | Try to solve @t1 = t2@
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
    <|> tryEqMulConst t1 t2
    <|> tryEqAddInf ctxt t1 t2
    <|> tryAddConst (=#=) t1 t2



-- | Try to solve @t1 /= t2@
cryIsNotEqual :: Ctxt -> Type -> Type -> Solved
cryIsNotEqual _i t1 t2 = matchDefault Unsolved (pBin PNeq (/=) t1 t2)

-- | Try to solve @t1 >= t2@
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
    <|> tryAddConst (>==) t1 t2
    <|> tryMinIsGeq t1 t2
    -- XXX: k >= width e
    -- XXX: width e >= k


  -- XXX: max t 10 >= 2 --> True
  -- XXX: max t 2 >= 10 --> a >= 10

-- | Try to solve something by evalutaion.
pBin :: PC -> (Nat' -> Nat' -> Bool) -> Type -> Type -> Match Solved
pBin tf p t1 t2 =
      Unsolvable <$> anError KNum t1
  <|> Unsolvable <$> anError KNum t2
  <|> (do x <- aNat' t1
          y <- aNat' t2
          return $ if p x y
                      then SolvedIf []
                      else Unsolvable $ TCErrorMessage
                        $ "Unsolvable constraint: " ++
                              show (pp (TCon (PC tf) [ tNat' x, tNat' y ])))


--------------------------------------------------------------------------------
-- GEQ

-- | Try to solve @K >= t@
tryGeqKThan :: Ctxt -> Type -> Nat' -> Match Solved
tryGeqKThan _ _ Inf = return (SolvedIf [])
tryGeqKThan _ ty (Nat n) =

  -- K1 >= K2 * t
  do (a,b) <- aMul ty
     m     <- aNat' a
     return $ SolvedIf
            $ case m of
                Inf   -> [ b =#= tZero ]
                Nat 0 -> []
                Nat k -> [ tNum (div n k) >== b ]

-- | Try to solve @t >= K@
tryGeqThanK :: Ctxt -> Type -> Nat' -> Match Solved
tryGeqThanK _ t Inf = return (SolvedIf [ t =#= tInf ])
tryGeqThanK _ t (Nat k) =

  -- K1 + t >= K2
  do (a,b) <- anAdd t
     n     <- aNat a
     return $ SolvedIf $ if n >= k
                            then []
                            else [ b >== tNum (k - n) ]


tryGeqThanSub :: Ctxt -> Type -> Type -> Match Solved
tryGeqThanSub _ x y =

  -- t1 >= t1 - t2
  do (a,_) <- (|-|) y
     guard (x == a)
     return (SolvedIf [])

tryGeqThanVar :: Ctxt -> Type -> TVar -> Match Solved
tryGeqThanVar _ctxt ty x =
  -- (t + a) >= a
  do (a,b) <- anAdd ty
     let check y = do x' <- aTVar y
                      guard (x == x')
                      return (SolvedIf [])
     check a <|> check b

-- | Try to prove GEQ by considering the known intervals for the given types.
geqByInterval :: Ctxt -> Type -> Type -> Match Solved
geqByInterval ctxt x y =
  let ix = typeInterval ctxt x
      iy = typeInterval ctxt y
  in case (iLower ix, iUpper iy) of
       (l,Just n) | l >= n -> return (SolvedIf [])
       _                   -> mzero

-- min K1 t >= K2 ~~> t >= K2, if K1 >= K2;  Err otherwise
tryMinIsGeq :: Type -> Type -> Match Solved
tryMinIsGeq t1 t2 =
  do (a,b) <- aMin t1
     k1    <- aNat a
     k2    <- aNat t2
     return $ if k1 >= k2
               then SolvedIf [ b >== t2 ]
               else Unsolvable $ TCErrorMessage $
                      show k1 ++ " can't be greater than " ++ show k2

--------------------------------------------------------------------------------


-- min t1 t2 = t1 ~> t1 <= t2
tryEqMin :: Type -> Type -> Match Solved
tryEqMin x y =
  do (a,b) <- aMin x
     let check m1 m2 = do guard (m1 == y)
                          return $ SolvedIf [ m2 >== m1 ]
     check a b <|> check b a


tryEqVar :: Type -> TVar -> Match Solved
tryEqVar ty x =

  -- a = K + a --> x = inf
  (do (k,tv) <- matches ty (anAdd, aNat, aTVar)
      guard (tv == x && k >= 1)

      return $ SolvedIf [ TVar x =#= tInf ]
  )
  <|>

  -- a = min (K + a) t --> a = t
  (do (l,r) <- aMin ty
      let check this other =
            do (k,x') <- matches this (anAdd, aNat', aTVar)
               guard (x == x' && k >= Nat 1)
               return $ SolvedIf [ TVar x =#= other ]
      check l r <|> check r l
  )
  <|>
  -- a = K + min t a
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

  -- (t1 + t2 = inf, fin t1) ~~~> t2 = inf
  do guard (lk == Inf)
     (a,b) <- anAdd ty
     let check x y = do guard (iIsFin (typeInterval ctxt x))
                        return $ SolvedIf [ y =#= tInf ]
     check a b <|> check b a
  <|>

  -- (K1 + t = K2, K2 >= K1) ~~~> t = (K2 - K1)
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
         -- Inf * t = Inf ~~~>  t >= 1
         (Inf,Inf)    -> SolvedIf [ b >== tOne ]

         -- K * t = Inf ~~~> t = Inf
         (Inf,Nat _)  -> SolvedIf [ b =#= tInf ]

         -- Inf * t = 0 ~~~> t = 0
         (Nat 0, Inf) -> SolvedIf [ b =#= tZero ]

         -- Inf * t = K ~~~> ERR      (K /= 0)
         (Nat k, Inf) -> Unsolvable
                       $ TCErrorMessage
                       $ show k ++ " /= inf * anything"

         (Nat lk', Nat rk')
           -- 0 * t = K2 ~~> K2 = 0
           | rk' == 0 -> SolvedIf [ tNat' lk =#= tZero ]
              -- shouldn't happen, as `0 * t = t` should have been simplified

           -- K1 * t = K2 ~~> t = K2/K1
           | (q,0) <- divMod lk' rk' -> SolvedIf [ b =#= tNum q ]
           | otherwise ->
               Unsolvable
             $ TCErrorMessage
             $ show lk ++ " /= " ++ show rk ++ " * anything"

  -- XXX: Min, Max, etx
  -- 2  = min (10,y)  --> y = 2
  -- 2  = min (2,y)   --> y >= 2
  -- 10 = min (2,y)   --> impossible


-- | K1 * t1 = K2 * t2
tryEqMulConst :: Type -> Type -> Match Solved
tryEqMulConst l r =
  do (l1,l2) <- aMul l
     (r1,r2) <- aMul r

     asum [ do l1' <- aNat l1
               r1' <- aNat r1
               return (build l1' l2 r1' r2)

          , do l2' <- aNat l2
               r1' <- aNat r1
               return (build l2' l1 r1' r2)

          , do l1' <- aNat l1
               r2' <- aNat r2
               return (build l1' l2 r2' r1)

          , do l2' <- aNat l2
               r2' <- aNat r2
               return (build l2' l1 r2' r1)

          ]

  where

  build lk l' rk r' =
    let d   = gcd lk rk
        lk' = lk `div` d
        rk' = rk `div` d
    in if d == 1
          then Unsolved
          else (SolvedIf [ tMul (tNum lk') l' =#= tMul (tNum rk') r' ])


-- | @(t1 + t2 = Inf, fin t1)  ~~> t2 = Inf@
tryEqAddInf :: Ctxt -> Type -> Type -> Match Solved
tryEqAddInf ctxt l r = check l r <|> check r l
  where

  -- check for x = a + b /\ x = inf
  check x y =
    do (x1,x2) <- anAdd x
       aInf y

       let x1Fin = iIsFin (typeInterval ctxt x1)
       let x2Fin = iIsFin (typeInterval ctxt x2)

       return $!
         if | x1Fin ->
              SolvedIf [ x2 =#= y ]

            | x2Fin ->
              SolvedIf [ x1 =#= y ]

            | otherwise ->
              Unsolved



-- | Check for addition of constants to both sides of a relation.
--  @((K1 + K2) + t1) `R` (K1 + t2)  ~~>   (K2 + t1) `R` t2@
--
-- This relies on the fact that constants are floated left during
-- simplification.
tryAddConst :: (Type -> Type -> Prop) -> Type -> Type -> Match Solved
tryAddConst rel l r =
  do (x1,x2) <- anAdd l
     (y1,y2) <- anAdd r

     k1 <- aNat x1
     k2 <- aNat y1

     if k1 > k2
        then return (SolvedIf [ tAdd (tNum (k1 - k2)) x2 `rel` y2 ])
        else return (SolvedIf [ x2 `rel` tAdd (tNum (k2 - k1)) y2 ])

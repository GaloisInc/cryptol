-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Solver code that does not depend on the type inference monad.

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.Numeric
  ( numericStep
  , simpFin
  , goalOrderModel
  ) where

import Cryptol.Utils.Panic(panic)

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Unify(mgu,Result(..))
import Cryptol.TypeCheck.Subst(fvs)
import Cryptol.TypeCheck.InferTypes(Goal(..), Solved(..))
import Cryptol.TypeCheck.Solver.FinOrd(OrdFacts, AssertResult(..),addFact)
import Cryptol.TypeCheck.Solver.Interval(Interval(..),iDisjoint)
import Cryptol.TypeCheck.Solver.Eval(typeInterval,simpType,
                                      typeKnownFin,typeKnownLeq,
                                      assumedOrderModel,
                                      derivedOrd
                                    )
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.TypeCheck.Solver.Utils

import Control.Monad(guard,msum)
import qualified Data.Set as Set


-- | Try to perform a single step of simplification for a
-- numeric goal.  We assume that the substitution has been applied to the
-- goal.
numericStep :: OrdFacts -> Goal -> Solved
numericStep m g =
  case tNoUser (simpType m (goal g)) of

    -- First we check if things are exactly the same, or we can
    -- substitutie in a variable (e.g., ?a = 1 + x)
    TCon (PC PEqual) [t1,t2]

       | OK (su,[]) <- unifier -> solvedS (Just su) []
       | Error _    <- unifier -> Unsolvable
         where unifier = mgu t1 t2

    TCon (PC PEqual) [t1,t2]

       -- Check if Inf is the only possible solution
       | Just prop <- checkOnlyInf m t1 t2 -> solved [prop]

       -- k1 + t1 = k2 + t2
       | Just (k1,t1') <- splitConstSummand t1
       , Just (k2,t2') <- splitConstSummand t2 ->
          let sub = case compare k1 k2 of
                      EQ -> t1' =#= t2'
                      LT -> t1' =#= (tNum (k2 - k1) .+. t2')
                      GT -> (tNum (k1 - k2) .+. t1') =#= t2'
          in solved [sub]

       -- fin a => a + t1 = a + t2
       | Just p <- eqByCancel m t1 t2 -> solved [p]

       -- k1 * t1 = k2 * t2
       | Just (k1,t1') <- splitConstFactor t1
       , Just (k2,t2') <- splitConstFactor t2
       , let c = gcd k1 k2
       , c > 1 -> solved [ tNum (div k1 c) .*. t1' =#= tNum (div k2 c) .*. t2' ]

       -- (x < b, x = min a b) => (x = a)
       | TCon (TF TCMin) [a,b] <- t1
       , Just ps <- simpEqMin m t2 a b  -> solved ps
       | TCon (TF TCMin) [a,b] <- t2
       , Just ps <- simpEqMin m t1 a b  -> solved ps

       -- (k >= 1, a = min (a + k, t)) => a = t
       | TVar a <- tNoUser t1
       , Just ps <- aIsMin m a (splitMins t2) -> solved ps

       | TVar a <- tNoUser t2
       , Just ps <- aIsMin m a (splitMins t1) -> solved ps

       -- (?x + s = t, s <= t, fin s) => (?x = t - s)
       -- useful as long as `?x` not in `fvs (s,t)`
       | Just ps <- eqBySub m t1 t2 -> solved ps

       -- Impossible
       | iDisjoint i1 i2 -> Unsolvable

       where i1 = typeInterval m t1
             i2 = typeInterval m t2


    -- We know these are not simple because they would have ended up
    -- in the OrdFacts
    TCon (PC PGeq) [t1,t2]
      | typeKnownLeq m t2 t1  -> solved []
      | otherwise             -> Unsolved

    prop | Just ps <- simpFin m prop -> solved ps

    _ -> Unsolved

  where
  solved = solvedS Nothing
  solvedS su xs = Solved su [ g { goal = x } | x <- xs ]


-- t1 == min t2 t3
simpEqMin :: OrdFacts -> Type -> Type -> Type -> Maybe [Prop]
simpEqMin m t1 t2 t3
  | t1 == t2              = Just [ t3 >== t1 ]    -- t1 = min t1 t3
  | t1 == t3              = Just [ t2 >== t1 ]    -- t1 = min t2 t1
  | knownSmaller m t1 t2  = Just [ t1 =#= t3 ]
  | knownSmaller m t1 t3  = Just [ t1 =#= t2 ]
  | otherwise             = Nothing

-- | Check to see if we know that `t1` is strictly smaller than `t2`
-- XXX: It'd be nice to combine this with knownLeq
-- XXX: There can be all kinds of rules here.
knownSmaller :: OrdFacts -> Type -> Type -> Bool
knownSmaller m t1 t2
  -- just a simple common case, arising from things like ([0] # something)
  | Just (_,t2') <- splitConstSummand t2
  , isFinite (typeInterval m t1)
  , t1 == t2' = True

knownSmaller _ _ _ = False


simpFin :: OrdFacts -> Prop -> Maybe [Prop]
simpFin m prop =
  case tNoUser prop of
    TCon (PC PFin) [ty] -> simpFinTy m ty
    _                   -> Nothing


simpFinTy :: OrdFacts -> Type -> Maybe [Prop]
simpFinTy _ ty | TCon (TC (TCNum _)) _ <- tNoUser ty = Just []
simpFinTy m ty | typeKnownFin m ty = Just []
simpFinTy m ty =
  case tNoUser ty of

    TCon (TF tf) [t1]
      | TCLg2    <- tf -> Just [pFin t1]
      | TCWidth  <- tf -> Just [pFin t1]

    TCon (TF tf) [t1,t2]
      | TCAdd <- tf -> Just [pFin t1, pFin t2]
      | TCSub <- tf -> Just [pFin t1]

      | TCMul <- tf
      , Nat n1 <- lowerBound i1, n1 >= 1
      , Nat n2 <- lowerBound i2, n2 >= 1
                    -> Just [pFin t1, pFin t2]

      | TCDiv <- tf -> Just [pFin t1]
      | TCMod <- tf -> Just []    -- hm
      | TCExp <- tf -> Just [pFin t1, pFin t2]
      | TCMin <- tf -> Nothing
      | TCMax <- tf -> Just [pFin t1, pFin t2]
      where i1 = typeInterval m t1
            i2 = typeInterval m t2


    TCon (TF tf) [_,_,_]
      | TCLenFromThen   <- tf -> Just []
      | TCLenFromThenTo <- tf -> Just []

    _ -> Nothing


{- | Detect equations of the form:

    a   = p + a   // fin p, p >= 1
    inf = p + a   // fin p
    inf = p * a   // fin p, p >= 1

The only solution to such equations is when `a = inf`, which is what we return.
When in doubt, it is OK to return `Nothing`
-}
checkOnlyInf :: OrdFacts -> Type -> Type -> Maybe Prop
checkOnlyInf ordM t1 t2 =
  case (tNoUser t1, tNoUser t2) of
    (TCon (TC TCInf) _, ty)                -> checkInf ty
    (ty,                TCon (TC TCInf) _) -> checkInf ty
    (TVar x,            ty)                -> checkVar x ty
    (ty, TVar x)                           -> checkVar x ty
    (_,_)                                  -> Nothing
  where
  checkVar a ty =
    do ty1 <- splitVarSummand a ty
       guard (validP 1 ty1)
       return (TVar a =#= tInf)

  validP lb p = let i = typeInterval ordM p
                in isFinite i && lowerBound i >= Nat lb

  checkInf ty = case ty of
                  TCon (TF TCAdd) [l,r]
                    | validP 0 l -> Just (r =#= tInf)
                    | validP 0 r -> Just (l =#= tInf)
                  TCon (TF TCMul) [l,r]
                    | validP 1 l -> Just (r =#= tInf)
                    | validP 1 r -> Just (l =#= tInf)
                  _ -> Nothing

-- (?x + s = t, fin s) <=> (t >= s, ?x = t - s)
-- useful as long as `?x` not in `fvs (s,t)`
eqBySub :: OrdFacts -> Type -> Type -> Maybe [Prop]
eqBySub ordM t1 t2 = msum $ zipWith attempt (splitVarSummands t1) (repeat t2) ++
                            zipWith attempt (splitVarSummands t2) (repeat t1)
  where
  attempt (x,s) t
    | not (x `Set.member` fvs (s,t)) && typeKnownFin ordM s =
      Just [ TVar x =#= (t .-. s), t >== s ]

    | otherwise = Nothing

-- (fin a, a + x == a + y) => (x == y)
eqByCancel :: OrdFacts -> Type -> Type -> Maybe Prop
eqByCancel ordM t1 t2 =
 msum [ check x | x <- Set.toList (fvs t1), typeKnownFin ordM (TVar x) ]
  where
  check x = do t1' <- splitVarSummand x t1
               t2' <- splitVarSummand x t2
               return (t1' =#= t2')


-- (a == min (k + a, t), k >= 1) => a == t
aIsMin :: OrdFacts -> TVar -> [Type] -> Maybe [Prop]
aIsMin _ _ []  = Nothing
aIsMin _ _ [_] = Nothing
aIsMin m a ts0 = attempt [] ts0
  where
  tMins []  = panic "Cryptol.TypeCheck.Solver.Numeric" [ "tMins []" ]
  tMins [t] = t
  tMins ts  = foldr1 tMin ts

  attempt _ [] = Nothing
  attempt others (t:ts)
    | isAparat m a t = Just [ TVar a =#= tMins (ts ++ others) ]
    | otherwise      = attempt (t:others) ts


-- Either this or splitVars summand could be fancier and go through functions
isAparat :: OrdFacts -> TVar -> Type -> Bool
isAparat m x ty = case splitVarSummand x ty of
                    Just t1 -> typeKnownLeq m (tNum (1::Int)) t1
                    _       -> False



-- | Collect `fin` and `<=` constraints in the ord model
-- Returns (new model, bad goals, other goals).
-- "bad goals" are goals that are incompatible with the model
-- "other goals" are ones that are not "<=" or "fin"
goalOrderModel :: OrdFacts -> [Goal] -> (OrdFacts, [Goal], [Goal])
goalOrderModel m0 todo =
  go m0 [] [] False [ g { goal = simpType m0 (goal g) } | g <- todo ]
  where
  go m bad others changes []
    | changes     = let (m1,newBad,newOthers) = goalOrderModel m others
                    in (m1, newBad ++ bad, newOthers)
    | otherwise   = case concatMap (derivedOrd m) (map goal others) of
                      [] -> (m,bad,others)
                      der -> case assumedOrderModel m der of
                               -- we know that these goals cannot be solved
                               -- but we don't have a good way to report the err
                               -- For now, we just leave the goals alone
                               Left _err -> (m,bad,others)

                               Right (m1,_) -> (m1,bad,others)

  go m bad others changes (g : gs)
    | Just ps <- simpFin m (goal g) =
        go m bad others changes ([ g { goal = p } | p <- ps ] ++ gs)

  go m bad others changes (g : gs) =
    case addFact g m of
      OrdAlreadyKnown   -> go m bad others changes gs
      OrdAdded m1       -> go m1 bad others True gs
      OrdCannot         -> go m bad (g : others) changes gs
      OrdImprove t1 t2  -> go m bad (g { goal = t1 =#= t2 } : others) changes gs
      OrdImpossible     -> go m (g : bad) others changes gs

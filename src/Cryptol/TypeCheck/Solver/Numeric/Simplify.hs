-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- TODO:
--  - Putting in a normal form to spot "prove by assumption"
--  - Additional simplification rules, namely various cancelation.
--  - Things like:  lg2 e(x) = x, where we know thate is increasing.

{-# LANGUAGE Safe, PatternGuards, BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Cryptol.TypeCheck.Solver.Numeric.Simplify
  (
  -- * Simplify a property
  crySimplify, crySimplifyMaybe

  -- * Simplify expressions in a prop
  , crySimpPropExpr, crySimpPropExprMaybe
  ) where

import           Cryptol.TypeCheck.Solver.Numeric.AST
import           Cryptol.TypeCheck.Solver.Numeric.SimplifyExpr
import           Cryptol.TypeCheck.Solver.InfNat(genLog,genRoot,rootExact)
import           Cryptol.Utils.Misc ( anyJust )

import           Control.Monad ( mplus )
import           Data.List ( sortBy )
import           Data.Maybe ( fromMaybe )
import qualified Data.Set as Set


-- | Simplify a property, if possible.
crySimplify :: Prop -> Prop
crySimplify p = fromMaybe p (crySimplifyMaybe p)

-- | Simplify a property, if possible.
crySimplifyMaybe :: Prop -> Maybe Prop
crySimplifyMaybe p =
  let mbSimpExprs = simpSubs p
      exprsSimped = fromMaybe p mbSimpExprs
      mbRearrange = tryRearrange exprsSimped
      rearranged  = fromMaybe exprsSimped mbRearrange
  in crySimplify `fmap` (crySimpStep rearranged `mplus` mbRearrange
                                                `mplus` mbSimpExprs)

  where
  tryRearrange q = case q of
                    _ :&& _ -> cryRearrangeAnd q
                    _ :|| _ -> cryRearrangeOr  q
                    _       -> Nothing

  simpSubs q = case q of
                Not a     -> Not `fmap` crySimplifyMaybe a
                a :&& b   -> do [a',b'] <- anyJust crySimplifyMaybe [a,b]
                                return (a' :&& b')
                a :|| b   -> do [a',b'] <- anyJust crySimplifyMaybe [a,b]
                                return (a' :|| b')
                _         -> crySimpPropExprMaybe q





-- | A single simplification step.
crySimpStep :: Prop -> Maybe Prop
crySimpStep prop =
  case prop of

    Fin x     -> cryIsFin x   -- Fin only on variables.

    x :== y   -> Just (cryIsEq x y)
    x :>  y   -> Just (cryIsGt x y)

    x :>= y   ->
      case (x,y) of
        -- XXX: DUPLICTION
        (K (Nat 0), _)       -> Just (y :== zero)
        (K (Nat a), Width b) -> Just (K (Nat (2 ^ a)) :>= b)

        (_,       K (Nat 0)) -> Just PTrue
        (Width e, K (Nat b)) -> Just (e :>= K (Nat (2^(b-1))))


        (K Inf, _)     -> Just PTrue
        (_, K Inf)     -> Just (x :== inf)
        _              -> Just (x :== inf :|| one :+ x :> y)

    x :==: y ->
      case (x,y) of
        (K a, K b)     -> Just (if a == b then PTrue else PFalse)
        (K (Nat n), _) | Just p <- cryIsNat True n y -> Just p
        (_, K (Nat n)) | Just p <- cryIsNat True n x -> Just p

        _ | x == y    -> Just PTrue
          | otherwise -> case (x,y) of
                           (Var _, _) -> Nothing
                           (_, Var _) -> Just (y :==: x)
                           _          -> Nothing

    x :>: y ->
      case (x,y) of
        (K (Nat n),_)  | Just p <- cryNatGt True n y -> Just p
        (_, K (Nat n)) | Just p <- cryGtNat True n x -> Just p

        _ | x == y      -> Just PFalse
          | otherwise   -> Nothing


    -- For :&& and :|| we assume that the props have been rearrnaged
    p :&& q -> cryAnd p q
    p :|| q -> cryOr p q

    Not p   -> cryNot p
    PFalse  -> Nothing
    PTrue   -> Nothing


-- | Rebalance parens, and arrange conjucts so that we can transfer
-- information left-to-right.
cryRearrangeAnd :: Prop -> Maybe Prop
cryRearrangeAnd prop =
  case rebalance prop of
    Just p  -> Just p
    Nothing -> cryAnds `fmap` cryRearrange cmpAnd (split prop)
  where
  rebalance (a :&& b) =
    case a of
      PFalse    -> Just PFalse
      PTrue     -> Just b
      a1 :&& a2 -> Just (a1 :&& (a2 :&& b))
      _         -> fmap (a :&&) (rebalance b)
  rebalance _ = Nothing

  split (a :&& b) = a : split b
  split a         = [a]


-- | Rebalance parens, and arrange disjuncts so that we can transfer
-- information left-to-right.
cryRearrangeOr :: Prop -> Maybe Prop
cryRearrangeOr prop =
  case rebalance prop of
    Just p  -> Just p
    Nothing -> cryOrs `fmap` cryRearrange cmpOr (split prop)
  where
  rebalance (a :|| b) =
    case a of
      PFalse    -> Just b
      PTrue     -> Just PTrue
      a1 :|| a2 -> Just (a1 :|| (a2 :|| b))
      _         -> fmap (a :||) (rebalance b)
  rebalance _ = Nothing

  split (a :|| b) = a : split b
  split a         = [a]




-- | Identify propositions that are suiatable for inlining.
cryIsDefn :: Prop -> Maybe (Name, Expr)
cryIsDefn (Var x :==: e) = if (x `Set.member` cryExprFVS e)
                              then Nothing
                              else Just (x,e)
cryIsDefn _              = Nothing





type PropOrdering = (Int,Prop) -> (Int,Prop) -> Ordering

{- | Rearrange proposition for conjuctions and disjunctions.

information left-to-right, so we put proposition with information content
on the left.
-}
cryRearrange :: PropOrdering -> [Prop] -> Maybe [Prop]
cryRearrange cmp ps = if ascending keys then Nothing else Just sortedProps
  where
  -- We tag each proposition with a number, so that later we can tell easily
  -- if the propositions got rearranged.
  (keys, sortedProps) = unzip (sortBy cmp (zip [ 0 :: Int .. ] ps))

  ascending (x : y : zs) = x < y && ascending (y : zs)
  ascending _            = True


cmpAnd :: PropOrdering
cmpAnd (k1,prop1) (k2,prop2) =
  case (prop1, prop2) of

    -- First comes PFalse, maybe we don't need to do anything
    (PFalse, PFalse) -> compare k1 k2
    (PFalse, _)      -> LT
    (_,PFalse)       -> GT

    -- Next comes PTrue
    (PTrue, PTrue)   -> compare k1 k2
    (PTrue, _)       -> LT
    (_,PTrue)        -> GT

    -- Next come `not (fin a)`  (i.e, a = inf)
    (Not (Fin (Var x)), Not (Fin (Var y))) -> cmpVars x y
    (Not (Fin (Var _)), _)                 -> LT
    (_, Not (Fin (Var _)))                 -> GT

    -- Next come defintions: `x = e` (with `x` not in `fvs e`)
    -- XXX: Inefficient, because we keep recomputing free variables
    -- (here, and then when actually applying the substitution)
    _ | Just (x,_) <- mbL
      , Just (y,_) <- mbR  -> cmpVars x y
      | Just _     <- mbL  -> LT
      | Just _     <- mbR  -> GT
      where
      mbL = cryIsDefn prop1
      mbR = cryIsDefn prop2

    -- Next come `fin a`
    (Fin (Var x), Fin (Var y)) -> cmpVars x y
    (Fin (Var _), _)           -> LT
    (_, Fin (Var _))           -> GT

    -- Everything else stays as is
    _ -> compare k1 k2

  where
  cmpVars x y
    | x < y     = LT
    | x > y     = GT
    | otherwise = compare k1 k2


cmpOr :: PropOrdering
cmpOr (k1,prop1) (k2,prop2) =
  case (prop1, prop2) of

    -- First comes PTrue, maybe we don't need to do anything
    (PTrue, PTrue)   -> compare k1 k2
    (PTrue, _)       -> LT
    (_,PTrue)        -> GT

    -- Next comes PFalse
    (PFalse, PFalse) -> compare k1 k2
    (PFalse, _)      -> LT
    (_,PFalse)       -> GT

    -- Next comes `fin a` (because we propagete `a = inf`)
    (Fin (Var x), Fin (Var y)) -> cmpVars x y
    (Fin (Var _), _)           -> LT
    (_, Fin (Var _))           -> GT

    -- Next come `not (fin a)`  (i.e, propagete (fin a))
    (Not (Fin (Var x)), Not (Fin (Var y))) -> cmpVars x y
    (Not (Fin (Var _)), _)                 -> LT
    (_, Not (Fin (Var _)))                 -> GT

    -- we don't propagete (x /= e) for now.

    -- Everything else stays as is
    _ -> compare k1 k2

  where
  cmpVars x y
    | x < y     = LT
    | x > y     = GT
    | otherwise = compare k1 k2





-- | Simplification of ':&&'.
-- Assumes arranged conjucntions.
-- See 'cryRearrangeAnd'.
cryAnd :: Prop -> Prop -> Maybe Prop
cryAnd p q =
  case p of
    PTrue       -> Just q

    PFalse      -> Just PFalse

    Not (Fin (Var x))
      | Just q' <- cryKnownFin x False q -> Just (p :&& q')

    Fin (Var x)
      | Just q' <- cryKnownFin x True q -> Just (p :&& q')

    _ | Just (x,e) <- cryIsDefn p
      , Just q'    <- cryLet x e q
      -> Just (p :&& q')

    _ -> Nothing


-- | Simplification of ':||'.
-- Assumes arranged disjunctions.
-- See 'cryRearrangeOr'
cryOr :: Prop -> Prop -> Maybe Prop
cryOr p q =
  case p of
    PTrue     -> Just PTrue

    PFalse    -> Just q

    Fin (Var x)
      | Just q' <- cryKnownFin x False q -> Just (p :|| q')

    Not (Fin (Var x))
      | Just q' <- cryKnownFin x True q -> Just (p :|| q')

    _ -> Nothing



-- | Propagate the fact that the variable is known to be finite ('True')
-- or not-finite ('False').
-- Note that this may introduce new expression redexes.
cryKnownFin :: Name -> Bool -> Prop -> Maybe Prop
cryKnownFin a isFin prop =
  case prop of
    Fin (Var a') | a == a' -> Just (if isFin then PTrue else PFalse)

    p :&& q -> do [p',q'] <- anyJust (cryKnownFin a isFin) [p,q]
                  return (p' :&& q')

    p :|| q -> do [p',q'] <- anyJust (cryKnownFin a isFin) [p,q]
                  return (p' :|| q')

    Not p   -> Not `fmap` cryKnownFin a isFin p

    x :==: y
      | not isFin, Just [x',y'] <- anyJust (cryLet a inf) [x,y]
      -> Just (cryNatOp (:==:) x' y')

    x :>: y
      | not isFin, Just [x',y'] <- anyJust (cryLet a inf) [x,y]
      -> Just (cryNatOp (:>:) x' y')

    -- All the other cases should be simplified, eventually.
    _       -> Nothing




-- | Negation.
cryNot :: Prop -> Maybe Prop
cryNot prop =
  case prop of
    Fin _           -> Nothing

    x :== y         -> Just (x :> y :|| y :> x)
    x :>= y         -> Just (y :>  x)
    x :>  y         -> Just (y :>= x)

    x :==: y        -> Just (x :>: y :|| y :>: x)

    _ :>: _         -> Nothing

    p :&& q         -> Just (Not p :|| Not q)
    p :|| q         -> Just (Not p :&& Not q)
    Not p           -> Just p
    PFalse          -> Just PTrue
    PTrue           -> Just PFalse



-- | Simplificaiton for @:==@
cryIsEq :: Expr -> Expr -> Prop
cryIsEq x y =
  case (x,y) of
    (K m, K n)      -> if m == n then PTrue else PFalse

    (K Inf, _)      -> Not (Fin y)
    (_, K Inf)      -> Not (Fin x)

    (Div x y, z)    -> x :>= z :* y :&& (one :+ z) :* y :> x

    (K (Nat n),_) | Just p <- cryIsNat False n y -> p
    (_,K (Nat n)) | Just p <- cryIsNat False n x -> p

    _               -> Not (Fin x) :&& Not (Fin y)
                   :|| Fin x :&& Fin y :&& cryNatOp (:==:) x y




-- | Simplificatoin for @:>@
cryIsGt :: Expr -> Expr -> Prop
cryIsGt (K m) (K n)   = if m > n then PTrue else PFalse
cryIsGt (K (Nat n)) e | Just p <- cryNatGt False n e = p
cryIsGt e (K (Nat n)) | Just p <- cryGtNat False n e = p

cryIsGt x y           = Fin y :&& (x :== inf :||
                                   Fin x :&& cryNatOp (:>:) x y)



-- | Attempt to simplify a @fin@ constraint.
-- Assumes a defined input.
cryIsFin :: Expr -> Maybe Prop
cryIsFin expr =
  case expr of
    K Inf                -> Just PFalse
    K (Nat _)            -> Just PTrue
    Var _                -> Nothing
    t1 :+ t2             -> Just (Fin t1 :&& Fin t2)
    t1 :- _              -> Just (Fin t1)

    t1 :* t2             -> Just ( Fin t1 :&& Fin t2
                               :|| t1 :== zero :&& t2 :== inf
                               :|| t2 :== zero :&& t1 :== inf
                                 )

    Div t1 _             -> Just (Fin t1)
    Mod _ _              -> Just PTrue

    t1 :^^ t2            ->
      Just ( Fin t1 :&& Fin t2
         :|| t1 :== inf :&& t2 :== zero   -- inf ^^ 0
         :|| t2 :== inf :&& (t1 :== zero :|| t1 :== one)
                             -- 0 ^^ inf,    1 ^^ inf
           )

    Min t1 t2            -> Just (Fin t1 :|| Fin t2)
    Max t1 t2            -> Just (Fin t1 :&& Fin t2)
    Width t1             -> Just (Fin t1)
    LenFromThen  _ _ _   -> Just PTrue
    LenFromThenTo  _ _ _ -> Just PTrue


cryIsNat :: Bool -> Integer -> Expr -> Maybe Prop
cryIsNat useFinite n expr =
  case expr of
    K Inf     -> Just PFalse

    K (Nat m) -> Just (if m == n then PTrue else PFalse)

    Var _ | useFinite   -> Nothing
          | otherwise   -> Just (Fin expr :&& expr :==: K (Nat n))

    K (Nat m) :+ e2     -> Just $ if m > n then PFalse
                                           else eq e2 $ K $ Nat $ n - m

    x :+ y
      | n == 0          -> Just (eq x zero :&& eq y zero)
      | n == 1          -> Just (eq x zero :&& eq y one :||
                                 eq x one  :&& eq y zero)
      | otherwise       -> Nothing

    e1 :- e2            -> Just $ eq (K (Nat n) :+ e1) e2

    K (Nat m) :* e2     ->
      Just $ if m == 0
                then if n == 0 then PTrue else PFalse
                else case divMod n m of
                       (q,r) -> if r == 0 then eq e2 (K (Nat q))
                                          else PFalse
    e1 :* e2
      | n == 0          -> Just (eq e1 zero :|| eq e2 zero)
      | n == 1          -> Just (eq e1 one :&& eq e2 one)
      | otherwise       -> Nothing

    -- (x >= n * y) /\ ((n+1) * y > x)
    Div x y             -> Just (gt (one :+ x) (K (Nat n) :* y) :&&
                                 gt (K (Nat (n + 1)) :* y) x)

    Mod _ _ | useFinite -> Nothing
            | otherwise -> Just (cryNatOp (:==:) expr (K (Nat n)))


    K (Nat m) :^^ y     -> Just $ case genLog n m of
                                    Just (a, exact)
                                      | exact -> eq y (K (Nat a))
                                    _ -> PFalse
    x :^^ K (Nat m)     -> Just $ case rootExact n m of
                                    Just a  -> eq x (K (Nat a))
                                    Nothing -> PFalse
    x :^^ y
      | n == 0          -> Just (eq x zero :&& gt y zero)
      | n == 1          -> Just (eq x one  :|| eq y zero)
      | otherwise       -> Nothing

    Min x y
      | n == 0          -> Just (eq x zero :|| eq y zero)
      | otherwise       -> Just ( eq x (K (Nat n)) :&& gt y (K (Nat (n - 1)))
                              :|| eq y (K (Nat n)) :&& gt x (K (Nat (n - 1)))
                                )

    Max x y             -> Just ( eq x (K (Nat n)) :&& gt (K (Nat (n + 1))) y
                              :|| eq y (K (Nat n)) :&& gt (K (Nat (n + 1))) y
                                )

    Width x
      | n == 0          -> Just (eq x zero)
      | otherwise       -> Just (gt x (K (Nat (2^(n-1) - 1))) :&&
                                 gt (K (Nat (2 ^ n))) x)

    LenFromThen x y w
      | n == 0          -> Just PFalse

      -- See Note [Sequences of Length 1] in 'Cryptol.TypeCheck.Solver.InfNat'
      | n == 1          -> Just (gt y x :&& gt (y :+ one) (two :^^ w))
      | otherwise       -> Nothing -- XXX: maybe some more?


    -- See `nLenFromThenTo` in 'Cryptol.TypeCheck.Solver.InfNat'
    LenFromThenTo x y z
      | n == 0          -> Just ( gt x y :&& gt z x
                              :|| gt y x :&& gt x z
                                )

      -- See Note [Sequences of Length 1] in 'Cryptol.TypeCheck.Solver.InfNat'
      | n == 1          -> Just (gt z y :&& gt (x :+ one) z     :||
                                 gt y z :&& gt (z :+ one) x)
      | otherwise       -> Nothing -- XXX: maybe some more?


  where
  eq x y = if useFinite then x :==: y else x :== y
  gt x y = if useFinite then x :>: y  else x :>  y

-- | Constant > expression
cryNatGt :: Bool -> Integer -> Expr -> Maybe Prop
cryNatGt useFinite n expr
  | n == 0    = Just PFalse
  | n == 1    = Just (eq expr zero)
  | otherwise =
    case expr of
      K x   -> Just $ if Nat n > x then PTrue else PFalse

      Var _ -> Nothing

      K (Nat m) :+ y -> Just $ if n >= m then gt (k (n - m)) y else PFalse
      _ :+ _         -> Nothing

      x :- y         -> Just $ gt (k n :+ y) x

      K (Nat m) :* y
        | m == 0    -> Just PTrue   -- because we know that n > 1
        | otherwise -> Just $ case divMod n m of
                                (q,0) -> gt (k q) y
                                (0,_) -> eq y zero
                                (q,_) -> gt (k (q + 1)) y
      _ :* _          -> Nothing

      Div x y         -> Just $ gt (k n :* y) x

      Mod _ (K (Nat m))
        | m <= n      -> Just PTrue

      Mod (K (Nat m)) _
        | m < n       -> Just PTrue
      Mod _ _         -> Nothing


      K (Nat m) :^^ y
        | m == 0      -> Just PTrue   -- because n > 1
        | m == 1      -> Just PTrue   -- ditto
        | otherwise   -> do (a,exact) <- genLog n m
                            return $ if exact
                                        then gt (k a) y
                                        else gt (k (a + 1)) y
      x :^^ K (Nat m)
        | m == 0      -> Just PTrue
        | m == 1      -> Just (gt (k n) x)
        | otherwise   -> do (a,exact) <- genRoot n m
                            return $ if exact
                                        then gt (k a) x
                                        else gt (k (a + 1)) x
      _ :^^ _         -> Nothing

      Min x y         -> Just $ gt (k n) x :|| gt (k n) y
      Max x y         -> Just $ gt (k n) x :&& gt (k n) y

      Width x         -> Just $ gt (k (2 ^ n)) x

      LenFromThen _ _ _   -> Nothing -- Are there some rules?

      LenFromThenTo _ _ _ -> Nothing -- Are there some rulesj

  where
  k x    = K (Nat x)
  eq x y = if useFinite then x :==: y else x :== y
  gt x y = if useFinite then x :>: y  else x :>  y



-- | Expression > constant
cryGtNat :: Bool -> Integer -> Expr -> Maybe Prop
cryGtNat useFinite n expr =
  case expr of
    K x                 -> Just $ if x > Nat n then PTrue else PFalse
    Var _               -> Nothing

    K (Nat m) :+ y
      | m > n           -> Just PTrue
      | otherwise       -> Just (gt y (K (Nat (n - m))))

    x :+ y
      | n == 0          -> Just (gt x zero :|| gt y zero)
      | otherwise       -> Nothing

    x :- y              -> Just $ gt x (K (Nat n) :+ y)


    K (Nat m) :* y
      | m > 0           -> Just $ case divMod n m of
                                    (a,_) -> gt y $ K $ Nat a

    x :* y
      | n == 0          -> Just (gt x zero :&& gt y zero)
      | otherwise       -> Nothing

    Div x y             -> Just $ gt (one :+ x) (K (Nat (n+1)) :* y)

    Mod _ (K (Nat m))
      | m <= n          -> Just PFalse
    Mod (K (Nat m)) _
      | m < n           -> Just PFalse
    Mod _ _             -> Nothing

    K (Nat m) :^^ y
      | m == 0          -> Just $ if n == 0 then eq y zero else PFalse
      | m == 1          -> Just $ if n == 0 then PTrue else PFalse
      | otherwise       -> do (a,_exact) <- genLog n m
                              Just (gt y (K (Nat a)))

    x :^^ K (Nat m)
      | m == 0          -> Just $ if n == 0 then PTrue else PFalse
      | m == 1          -> Just $ gt x (K (Nat n))
      | otherwise       -> do (a,exact) <- genRoot n m
                              Just $ if exact
                                        then gt x (K (Nat a))
                                        else gt (one :+ x) (K (Nat (a+1)))

    x :^^ y
      | n == 0          -> Just (gt x zero :|| eq y zero)
      | otherwise       -> Nothing

    Min x y             -> Just $ gt x (K (Nat n)) :&& gt y (K (Nat n))
    Max x y             -> Just $ gt x (K (Nat n)) :|| gt y (K (Nat n))

    Width x             -> Just $ gt (one :+ x) (K (Nat (2 ^ n)))

    LenFromThen _ _ _
      | n == 0          -> Just PTrue
      | otherwise       -> Nothing -- Are there some rules?

    LenFromThenTo x y z
      | n == 0          -> Just (gt x y :&& gt z x :|| gt y x :&& gt x z)
      | otherwise       -> Nothing

  where
  eq x y = if useFinite then x :==: y else x :== y
  gt x y = if useFinite then x :>: y  else x :>  y



-- | Simplify only the Expr parts of a Prop.
crySimpPropExpr :: Prop -> Prop
crySimpPropExpr p = fromMaybe p (crySimpPropExprMaybe p)

-- | Simplify only the Expr parts of a Prop.
-- Returns `Nothing` if there were no changes.
crySimpPropExprMaybe  :: Prop -> Maybe Prop
crySimpPropExprMaybe prop =
  case prop of

    Fin e                 -> Fin `fmap` crySimpExprMaybe e

    a :==  b              -> binop crySimpExprMaybe (:== ) a b
    a :>=  b              -> binop crySimpExprMaybe (:>= ) a b
    a :>   b              -> binop crySimpExprMaybe (:>  ) a b
    a :==: b              -> binop crySimpExprMaybe (:==:) a b
    a :>:  b              -> binop crySimpExprMaybe (:>: ) a b

    a :&& b               -> binop crySimpPropExprMaybe (:&&) a b
    a :|| b               -> binop crySimpPropExprMaybe (:||) a b

    Not p                 -> Not `fmap` crySimpPropExprMaybe p

    PFalse                -> Nothing
    PTrue                 -> Nothing

  where

  binop simp f l r =
    case (simp l, simp r) of
      (Nothing,Nothing) -> Nothing
      (l',r')           -> Just (f (fromMaybe l l') (fromMaybe r r'))






-- | Our goal is to bubble @inf@ terms to the top of @Return@.
cryNoInf :: Expr -> IfExpr Expr
cryNoInf expr =
  case expr of

    -- These are the interesting cases where we have to branch

    x :* y ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x', y') of
           (K Inf, K Inf) -> return inf
           (K Inf, _)     -> mkIf (y' :==: zero) (return zero) (return inf)
           (_, K Inf)     -> mkIf (x' :==: zero) (return zero) (return inf)
           _              -> return (x' :* y')

    x :^^ y ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x', y') of
           (K Inf, K Inf) -> return inf
           (K Inf, _)     -> mkIf (y' :==: zero) (return one) (return inf)
           (_, K Inf)     -> mkIf (x' :==: zero) (return zero)
                           $ mkIf (x' :==: one)  (return one)
                           $ return inf
           _              -> return (x' :^^ y')



    -- The rest just propagates

    K _     -> return expr
    Var _   -> return expr

    x :+ y  ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x', y') of
           (K Inf, _)  -> return inf
           (_, K Inf)  -> return inf
           _           -> return (x' :+ y')

    x :- y  ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x', y') of
           (_, K Inf)  -> Impossible
           (K Inf, _)  -> return inf
           _           -> mkIf (x' :==: y)
                               (return zero)
                               (mkIf (x' :>: y) (return (x' :- y'))
                                                Impossible)

    Div x y ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x', y') of
           (K Inf, _) -> Impossible
           (_, K Inf) -> return zero
           _          -> mkIf (y' :>: zero) (return (Div x' y')) Impossible

    Mod x y ->
      do x' <- cryNoInf x
         -- `Mod x y` is finite, even if `y` is `inf`, so first check
         -- for finiteness.
         mkIf (Fin y)
              (do y' <- cryNoInf y
                  case (x',y') of
                    (K Inf, _) -> Impossible
                    (_, K Inf) -> Impossible
                    _ -> mkIf (y' :>: zero) (return (Mod x' y')) Impossible
              )
              (return x')

    Min x y ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x',y') of
           (K Inf, _) -> return y'
           (_, K Inf) -> return x'
           _          -> return (Min x' y')

    Max x y ->
      do x' <- cryNoInf x
         y' <- cryNoInf y
         case (x', y') of
           (K Inf, _) -> return inf
           (_, K Inf) -> return inf
           _          -> return (Max x' y')

    Width x ->
      do x' <- cryNoInf x
         case x' of
           K Inf      -> return inf
           _          -> return (Width x')

    LenFromThen x y w   -> fun3 LenFromThen x y w
    LenFromThenTo x y z -> fun3 LenFromThenTo x y z


  where
  fun3 f x y z =
    do x' <- cryNoInf x
       y' <- cryNoInf y
       z' <- cryNoInf z
       case (x',y',z') of
         (K Inf, _, _) -> Impossible
         (_, K Inf, _) -> Impossible
         (_, _, K Inf) -> Impossible
         _             -> mkIf (x' :==: y') Impossible
                                            (return (f x' y' z'))

  mkIf p t e = case crySimplify p of
                 PTrue  -> t
                 PFalse -> e
                 p'     -> If p' t e




-- | Make an expression that should work ONLY on natural nubers.
-- Eliminates occurances of @inf@.
-- Assumes that the two input expressions are well-formed and finite.
-- The expression is constructed by the given function.
cryNatOp :: (Expr -> Expr -> Prop) -> Expr -> Expr -> Prop
cryNatOp op x y =
  toProp $
  do x' <- noInf x
     y' <- noInf y
     return (op x' y')
  where
  noInf a = do a' <- cryNoInf a
               case a' of
                 K Inf -> Impossible
                 _     -> return a'

  toProp ite =
    case ite of
      Impossible -> PFalse -- It doesn't matter, but @false@ might anihilate.
      Return p   -> p
      If p t e   -> p :&& toProp t :|| Not p :&& toProp e




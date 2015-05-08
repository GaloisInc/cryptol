{-# LANGUAGE Safe, PatternGuards, BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- | Simplification.
The rules in this module are all conditional on the expressions being
well-defined.

So, for example, consider the formula `P`, which corresponds to `fin e`.
`P` says the following:

    if e is well-formed, then will evaluate to a finite natural number.

More concretely, consider `fin (3 - 5)`.  This will be simplified to `True`,
which does not mean that `3 - 5` is actually finite.
-}

module Cryptol.TypeCheck.Solver.Numeric.Simplify1 (propToProp', ppProp') where

import           Cryptol.TypeCheck.Solver.Numeric.SimplifyExpr
                   (crySimpExpr, splitSum, normSum, Sign(..))
import           Cryptol.TypeCheck.Solver.Numeric.AST
import           Cryptol.Utils.Misc ( anyJust )

import           Control.Monad ( liftM2 )
import           Data.Maybe ( fromMaybe )
import qualified Data.Map as Map
import           Text.PrettyPrint
import           Data.Either(partitionEithers)



data Atom = AFin Name
          | AGt Expr Expr   -- on naturals
          | AEq Expr Expr   -- on naturals
            deriving Eq

type I    = IfExpr' Atom


-- tmp
propToProp' :: Prop -> I Bool
propToProp' prop =
  case prop of
    Fin e     -> pFin e
    x :== y   -> pEq x y
    x :>= y   -> pGeq x y
    x :>  y   -> pGt  x y
    x :>: y   -> pAnd (pFin x) (pAnd (pFin y) (pGt x y))
    x :==: y  -> pAnd (pFin x) (pAnd (pFin y) (pEq x y))
    p :&& q   -> pAnd (propToProp' p) (propToProp' q)
    p :|| q   -> pOr  (propToProp' p) (propToProp' q)
    Not p     -> pNot (propToProp' p)
    PFalse    -> pFalse
    PTrue     -> pTrue


instance (Eq a, HasVars a) => HasVars (I a) where
  apSubst su prop =
    case prop of
      Impossible -> Nothing
      Return _   -> Nothing
      If a t e   ->
        case apSubstAtom su a of
          Nothing -> do [x,y] <- branches
                        return (If a x y)
          Just a' -> Just $ fromMaybe (pIf a' t e)
                          $ do [x,y] <- branches
                               return (pIf a' x y)

        where branches = anyJust (apSubst su) [t,e]

-- | Apply a substituition to an atom
apSubstAtom :: Subst -> Atom -> Maybe (I Bool)
apSubstAtom su atom =
  case atom of
    AFin x    -> do e <- Map.lookup x su
                    return (pFin e)
    AEq e1 e2 -> do [x,y] <- anyJust (apSubst su) [e1,e2]
                    return (pEq x y)
    AGt e1 e2 -> do [x,y] <- anyJust (apSubst su) [e1,e2]
                    return (pGt x y)


-- | The various way in which the given proposition may be true.
-- The Boolean indicates if the atom is +ve:
-- 'True' for positive, 'False' for -ve.
truePaths :: I Bool -> [ [(Bool,Atom)] ]
truePaths prop =
  case prop of
    Impossible    -> []
    Return False  -> []
    Return True   -> [ [] ]
    If a t e      -> map ((True,a):)  (truePaths t) ++
                     map ((False,a):) (truePaths e)



--------------------------------------------------------------------------------
-- Pretty print

ppAtom :: Atom -> Doc
ppAtom atom =
  case atom of
    AFin x  -> text "fin" <+> ppName x
    AGt x y -> ppExpr x <+> text ">" <+> ppExpr y
    AEq x y -> ppExpr x <+> text "=" <+> ppExpr y

ppProp' :: I Bool -> Doc
ppProp' = ppIf ppAtom (text . show)

--------------------------------------------------------------------------------
-- General logic stuff

-- | False
pFalse :: I Bool
pFalse = Return False

-- | True
pTrue :: I Bool
pTrue = Return True

-- | Negation
pNot :: I Bool -> I Bool
pNot p =
  case p of
    Impossible -> Impossible
    Return a   -> Return (not a)
    If c t e   -> If c (pNot t) (pNot e)

-- | And
pAnd :: I Bool -> I Bool -> I Bool
pAnd p q = pIf p q pFalse

-- | Or
pOr :: I Bool -> I Bool -> I Bool
pOr p q = pIf p pTrue q


mkIf :: (Eq a, HasVars a) => Atom -> I a -> I a -> I a
mkIf a t e
  | t == e    = t
  | otherwise = case a of
                  AFin x -> If a (pKnownFin x t) (pKnownInf x e)
                  AEq x' y'
                    | x == y  -> t
                    | otherwise -> If (AEq x y) t e
                    where (x,y) = balanceEq x' y'


                  _      -> If a t e


-- | If-then-else with non-atom at decision.
pIf :: (Eq a, HasVars a) => I Bool -> I a -> I a -> I a
pIf c t e =
  case c of
    Impossible    -> Impossible
    Return True   -> t
    Return False  -> e
    If p t1 e1
      | t2 == e2  -> t2
      | otherwise -> mkIf p t2 e2
      where
      t2 = pIf t1 t e
      e2 = pIf e1 t e

-- | Atoms to propositions.
pAtom :: Atom -> I Bool
pAtom p = do a <- case p of
                    AFin _  -> return p
                    AEq x y -> bin AEq x y
                    AGt x y -> bin AGt x y
             If a pTrue pFalse
  where
  prep x    = do y <- eNoInf x
                 case y of
                   K Inf -> Impossible
                   _     -> return (crySimpExpr y)
  bin f x y = liftM2 f (prep x) (prep y)




--------------------------------------------------------------------------------
-- Implementation of Cryptol constraints

-- | Implementation of `==`
pEq :: Expr -> Expr -> I Bool
pEq x (K (Nat 0)) = pEq0 x
pEq x (K (Nat 1)) = pEq1 x
pEq (K (Nat 0)) y = pEq0 y
pEq (K (Nat 1)) y = pEq1 y
pEq x y = pIf (pInf x) (pInf y)
        $ pAnd (pFin y) (pAtom (AEq x y))

-- | Implementation of `>=`
pGeq :: Expr -> Expr -> I Bool
pGeq x y = pIf (pInf x) pTrue
         $ pIf (pFin y) (pAtom (AGt (x :+ one) y))
           pFalse

-- | Implementation of `Fin`
pFin :: Expr -> I Bool
pFin expr =
  case expr of
    K Inf                -> pFalse
    K (Nat _)            -> pTrue
    Var x                -> pAtom (AFin x)
    t1 :+ t2             -> pAnd (pFin t1) (pFin t2)
    t1 :- _              -> pFin t1
    t1 :* t2             -> pIf (pInf t1) (pEq t2 zero)
                          $ pIf (pInf t2) (pEq t1 zero)
                          $ pTrue

    Div t1 _             -> pFin t1
    Mod _ _              -> pTrue

    t1 :^^ t2            -> pIf (pInf t1) (pEq t2 zero)
                          $ pIf (pInf t2) (pOr (pEq t1 zero) (pEq t1 one))
                          $ pTrue


    Min t1 t2            -> pOr (pFin t1) (pFin t2)
    Max t1 t2            -> pAnd (pFin t1) (pFin t2)
    Lg2 t1               -> pFin t1
    Width t1             -> pFin t1
    LenFromThen  _ _ _   -> pTrue
    LenFromThenTo  _ _ _ -> pTrue

-- | Implementation `e1 > e2`.
pGt :: Expr -> Expr -> I Bool
pGt x y = pIf (pFin y) (pIf (pFin x) (pAtom (AGt x y)) pTrue) pFalse

-- | Implementation of `e == inf`
pInf :: Expr -> I Bool
pInf = pNot . pFin



-- | Special case: `e == 0`
pEq0 :: Expr -> I Bool
pEq0 expr =
  case expr of
    K Inf               -> pFalse
    K (Nat n)           -> if n == 0 then pTrue else pFalse
    Var _               -> pAnd (pFin expr) (pAtom (AEq expr zero))
    t1 :+ t2            -> pAnd (pEq t1 zero) (pEq t2 zero)
    t1 :- t2            -> pEq t1 t2
    t1 :* t2            -> pOr (pEq t1 zero) (pEq t2 zero)
    Div t1 t2           -> pGt t2 t1
    Mod _ _             -> pAtom (AEq expr zero)  -- or divides
    t1 :^^ t2           -> pIf (pEq t2 zero) pFalse (pEq t1 zero)
    Min t1 t2           -> pOr  (pEq t1 zero) (pEq t2 zero)
    Max t1 t2           -> pAnd (pEq t1 zero) (pEq t2 zero)
    Lg2 t1              -> pOr  (pEq t1 zero) (pEq t1 one)
    Width t1            -> pEq t1 zero
    LenFromThen _ _ _   -> pFalse
    LenFromThenTo x y z -> pIf (pGt x y) (pGt z x) (pGt x z)

-- | Special case: `e == 1`
pEq1 :: Expr -> I Bool
pEq1 expr =
  case expr of
    K Inf               -> pFalse
    K (Nat n)           -> if n == 1 then pTrue else pFalse
    Var _               -> pAnd (pFin expr) (pAtom (AEq expr one))
    t1 :+ t2            -> pIf (pEq t1 zero) (pEq t2 one)
                         $ pIf (pEq t2 zero) (pEq t1 one) pFalse
    t1 :- t2            -> pEq t1 (t2 :+ one)
    t1 :* t2            -> pAnd (pEq t1 one) (pEq t2 one)
    Div t1 t2           -> pAnd (pGt (two :* t2) t1) (pGeq t1 t2)
    Mod _ _             -> pAtom (AEq expr one)
    t1 :^^ t2           -> pOr (pEq t1 one) (pEq t2 zero)

    Min t1 t2           -> pIf (pEq t1 one) (pGt t2 zero)
                         $ pIf (pEq t2 one) (pGt t1 zero)
                           pFalse
    Max t1 t2           -> pIf (pEq t1 one) (pGt two t2)
                         $ pIf (pEq t2 one) (pGt two t1)
                           pFalse

    Lg2 t1              -> pEq t1 two
    Width t1            -> pEq t1 one

    -- See Note [Sequences of Length 1] in 'Cryptol.TypeCheck.Solver.InfNat'
    LenFromThen x y w   -> pAnd (pGt y x) (pGeq y (two :^^ w))
    LenFromThenTo x y z -> pIf (pGt z y) (pGeq x z) (pGeq z x)

--------------------------------------------------------------------------------

pKnownFin :: (HasVars a, Eq a) => Name -> I a -> I a
pKnownFin x prop =
  case prop of
    If (AFin y) t _
      | x == y  -> pKnownFin x t
    If p t e    -> mkIf p (pKnownFin x t) (pKnownFin x e)
    _ -> prop

pKnownInf :: (Eq a, HasVars a) => Name -> I a -> I a
pKnownInf x prop = fromMaybe prop (apSubst (Map.singleton x (K Inf)) prop)






-- Cancel constants
-- If the original equation was valid, it continues to be valid.
balanceEq :: Expr -> Expr -> (Expr, Expr)
balanceEq (K (Nat a) :+ e1) (K (Nat b) :+ e2)
  | a >= b    = balanceEq e2 (K (Nat (a - b)) :+ e1)
  | otherwise = balanceEq e1 (K (Nat (b - a)) :+ e2)

-- Move subtraction to the other side.
-- If the original equation was valid, this will continue to be valid.
balanceEq e1 e2
  | not (null neg_es1 && null neg_es2) = balanceEq (mk neg_es2 pos_es1)
                                                   (mk neg_es1 pos_es2)

  where
  (pos_es1, neg_es1)  = partitionEithers (map classify (splitSum e1))
  (pos_es2, neg_es2)  = partitionEithers (map classify (splitSum e2))

  classify (sign,e)   = case sign of
                          Pos -> Left e
                          Neg -> Right e

  mk as bs = normSum (foldr (:+) zero (as ++ bs))

-- fallback
balanceEq x y = (x,y)




balanceGt (K (Nat a) :+ e1) (K (Nat b) :+ e2)
  | a >= b    = balanceGt (K (Nat (a - b)) :+ e1) e2
  | otherwise = balanceGt e1                      (K (Nat (b - a)) :+ e2)






--------------------------------------------------------------------------------

-- | Eliminate `inf`, except at the top level.
eNoInf :: Expr -> I Expr
eNoInf expr =
  case expr of

    -- These are the interesting cases where we have to branch

    x :* y ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x', y') of
           (K Inf, K Inf) -> return inf
           (K Inf, _)     -> pIf (pEq y' zero) (return zero) (return inf)
           (_, K Inf)     -> pIf (pEq x' zero) (return zero) (return inf)
           _              -> return (x' :* y')

    x :^^ y ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x', y') of
           (K Inf, K Inf) -> return inf
           (K Inf, _)     -> pIf (pEq y' zero) (return one) (return inf)
           (_, K Inf)     -> pIf (pEq x' zero) (return zero)
                           $ pIf (pEq x' one)  (return one)
                           $ return inf
           _              -> return (x' :^^ y')


    -- The rest just propagates

    K _     -> return expr
    Var _   -> return expr

    x :+ y  ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x', y') of
           (K Inf, _)  -> return inf
           (_, K Inf)  -> return inf
           _           -> return (x' :+ y')

    x :- y  ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x', y') of
           (_, K Inf)  -> Impossible
           (K Inf, _)  -> return inf
           _           -> return (x' :- y')

    Div x y ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x', y') of
           (K Inf, _) -> Impossible
           (_, K Inf) -> return zero
           _          -> return (Div x' y')

    Mod x y ->
      do x' <- eNoInf x
         -- `Mod x y` is finite, even if `y` is `inf`, so first check
         -- for finiteness.
         pIf (pFin y)
              (do y' <- eNoInf y
                  case (x',y') of
                    (K Inf, _) -> Impossible
                    (_, K Inf) -> Impossible
                    _          -> return (Mod x' y')
              )
              (return x')

    Min x y ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x',y') of
           (K Inf, _) -> return y'
           (_, K Inf) -> return x'
           _          -> return (Min x' y')

    Max x y ->
      do x' <- eNoInf x
         y' <- eNoInf y
         case (x', y') of
           (K Inf, _) -> return inf
           (_, K Inf) -> return inf
           _          -> return (Max x' y')

    Lg2 x ->
      do x' <- eNoInf x
         case x' of
           K Inf     -> return inf
           _         -> return (Lg2 x')

    Width x ->
      do x' <- eNoInf x
         case x' of
           K Inf      -> return inf
           _          -> return (Width x')

    LenFromThen x y w   -> fun3 LenFromThen x y w
    LenFromThenTo x y z -> fun3 LenFromThenTo x y z


  where
  fun3 f x y z =
    do x' <- eNoInf x
       y' <- eNoInf y
       z' <- eNoInf z
       case (x',y',z') of
         (K Inf, _, _) -> Impossible
         (_, K Inf, _) -> Impossible
         (_, _, K Inf) -> Impossible
         _             -> return (f x' y' z')



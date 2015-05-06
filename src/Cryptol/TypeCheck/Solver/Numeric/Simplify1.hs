{-# LANGUAGE Safe, PatternGuards, BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
-- | Simplification.
-- TODO:
--  - Putting in a normal form to spot "prove by assumption"
--  - Additional simplification rules, namely various cancelation.
--  - Things like:  lg2 e(x) = x, where we know thate is increasing.

module Cryptol.TypeCheck.Solver.Numeric.Simplify1 (propToProp', ppProp') where

import           Cryptol.TypeCheck.Solver.Numeric.AST
import qualified Cryptol.TypeCheck.Solver.InfNat as IN
import           Cryptol.Utils.Misc ( anyJust )

import           Control.Monad ( liftM2 )
import           Data.Maybe ( fromMaybe )
import qualified Data.Map as Map
import           Text.PrettyPrint



data Atom = AFin Name
          | AGt Expr Expr   -- on naturals
          | AEq Expr Expr   -- on naturals
            deriving Eq

type Prop' = IfExpr' Atom Bool

-- tmp
propToProp' :: Prop -> Prop'
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


--------------------------------------------------------------------------------
-- Pretty print

ppAtom :: Atom -> Doc
ppAtom atom =
  case atom of
    AFin x  -> text "fin" <+> ppName x
    AGt x y -> ppExpr x <+> text ">" <+> ppExpr y
    AEq x y -> ppExpr x <+> text "=" <+> ppExpr y

ppProp' :: Prop' -> Doc
ppProp' = ppIf ppAtom (text . show)

--------------------------------------------------------------------------------
-- General logic stuff

-- | False
pFalse :: Prop'
pFalse = Return False

-- | True
pTrue :: Prop'
pTrue = Return True

-- | Negation
pNot :: Prop' -> Prop'
pNot p =
  case p of
    Impossible -> Impossible
    Return a   -> Return (not a)
    If c t e   -> If c (pNot t) (pNot e)

-- | And
pAnd :: Prop' -> Prop' -> Prop'
pAnd p q = pIf p q pFalse

-- | Or
pOr :: Prop' -> Prop' -> Prop'
pOr p q = pIf p pTrue q


-- | If-then-else with non-atom at decision.
pIf :: (Eq a, Eq p) =>
        IfExpr' p Bool -> IfExpr' p a -> IfExpr' p a -> IfExpr' p a
pIf c t e =
  case c of
    Impossible    -> Impossible
    Return True   -> t
    Return False  -> e
    _ | t == e    -> t -- slow for large expressions
    If p t1 e1
      | t2 == e2  -> t2
      | otherwise -> If p t2 e2
      where
      t2 = pIf t1 t e
      e2 = pIf e1 t e

-- | Atoms to propositions.
pAtom :: Atom -> Prop'
pAtom p = do a <- case p of
                    AFin _  -> return p
                    AEq x y -> liftM2 AEq (eNoInf x) (eNoInf y)
                    AGt x y -> liftM2 AGt (eNoInf x) (eNoInf y)
             If a pTrue pFalse




--------------------------------------------------------------------------------
-- Implementation of Cryptol constraints

-- | Implementation of `==`
pEq :: Expr -> Expr -> Prop'
pEq x (K (Nat 0)) = pEq0 x
pEq x (K (Nat 1)) = pEq1 x
pEq (K (Nat 0)) y = pEq0 y
pEq (K (Nat 1)) y = pEq1 y
pEq x y = pIf (pInf x) (pInf y)
        $ pAnd (pFin y) (pAtom (AEq x y))

-- | Implementation of `>=`
pGeq :: Expr -> Expr -> Prop'
pGeq x y = pIf (pInf x) pTrue
         $ pIf (pFin y) (pAtom (AGt (x :+ one) y))
           pFalse

-- | Implementation of `Fin` on expressions.
pFin :: Expr -> Prop'
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

-- | Implement `e1 > e2`.
pGt :: Expr -> Expr -> Prop'
pGt x y = pIf (pFin y) (pIf (pFin x) (pAtom (AGt x y)) pTrue) pFalse

-- `e == inf`
pInf :: Expr -> Prop'
pInf = pNot . pFin



-- | Special rules implementing `e == 0`
--   Assuming the original expression was well-formed.
pEq0 :: Expr -> Prop'
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

-- | Special rules implementing `e == 1`
--   Assuming the original expression was well-formed.
pEq1 :: Expr -> Prop'
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

{-
aSimplify :: Atom -> Either Atom Bool
aSimplify atom =
  case atom of
    AFin _    -> Left atom

    AEq e1 e2
      | e1' == e2'              -> Right True
      | K _ <- e1', K _ <- e2'  -> Right False


      -- Move variables to one side
      -- Cancel common factors
      | otherwise               -> Left (AEq e1' e2')

      where
      e1' = crySimpExpr e1
      e2' = crySimpExpr e2

    AGt e1 e2
      | K (Nat 0) <- e1'        -> Right False

      where
      e1' = crySimpExpr e1
      e2' = crySimpExpr e2

balanceEq (K (Nat a) :+ e1) (K (Nat b) :+ e2)
  | a >= b    = balanceEq e2 (K (Nat (a - b)) :+ e1)
  | otherwise = balanceEq e1 (K (Nat (b - a)) :+ e2)

-}






instance HasVars Prop' where
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
apSubstAtom :: Subst -> Atom -> Maybe Prop'
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
truePaths :: Prop' -> [ [(Bool,Atom)] ]
truePaths prop =
  case prop of
    Impossible    -> []
    Return False  -> []
    Return True   -> [ [] ]
    If a t e      -> map ((True,a):)  (truePaths t) ++
                     map ((False,a):) (truePaths e)

--------------------------------------------------------------------------------

type IExpr = IfExpr' Atom Expr

-- | Our goal is to bubble @inf@ terms to the top of @Return@.
eNoInf :: Expr -> IExpr
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



{-# LANGUAGE Safe, PatternGuards #-}
module Cryptol.TypeCheck.Solver.CrySAT1 where

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Text.PrettyPrint

test = ( ppExpr e2
       , ppProp
          $ crySimpProp
          $ cryDefined e2
       )

  where expr = Div (K (Nat 2) :* Var (Name 0)) (Var (Name 1))
        e2  = Max (Var (Name 0)) (K Inf)


--------------------------------------------------------------------------------
newtype Name = Name Int
              deriving (Eq,Show)

infixr 2 :||
infixr 3 :&&
infix  4 :==, :/=, :>, :>=
infixl 6 :+, :-
infixl 7 :*
infixr 8 :^^

-- | Propopsitions, representing Cryptol's numeric constraints (and a bit more).
data Prop = Fin Expr
          | Expr :== Expr | Expr :/= Expr
          | Expr :>= Expr | Expr :> Expr
          | Prop :&& Prop | Prop :|| Prop
          | Not Prop
          | PFalse | PTrue
            deriving Show

-- | Expressions, representing Cryptol's numeric types.
data Expr = K Nat'
          | Var Name
          | Expr :+ Expr
          | Expr :- Expr
          | Expr :* Expr
          | Div Expr Expr
          | Mod Expr Expr
          | Expr :^^ Expr
          | Min Expr Expr
          | Max Expr Expr
          | Lg2 Expr
          | Width Expr
          | LenFromThen   Expr Expr Expr
          | LenFromThenTo Expr Expr Expr
            deriving Show


cryLetProp :: Name -> Expr -> Prop -> Prop
cryLetProp a e prop =
  case prop of
    Fin x   -> Fin (cryLet x e x)
    x :== y -> cryLet a e x 



cryAnd :: Prop -> Prop -> Prop
cryAnd p q =
  case p of
    PTrue       -> q
    PFalse      -> PFalse
    p1 :&& p2   -> cryAnd p1 (p2 :&& q)

    _ -> case q of
           PTrue  -> p
           PFalse -> PFalse
           _      ->

             case p of
               Var x :== t -> p :&& cryLetProp x t q

cryOr :: Prop -> Prop -> Prop
cryOr p q =
  case p of
    PTrue  -> PTrue
    PFalse -> q
    _ -> case q of
           PTrue  -> PTrue
           PFalse -> q
           _      -> p :|| q


-- | Eliminate 'Not', and nested 'PFalse' and 'PTrue'.
crySimpProp :: Prop -> Prop
crySimpProp prop =
  case prop of

    p :&& q ->
      case crySimpProp p of
        PTrue  -> crySimpProp q
        PFalse -> PFalse
        p'     -> case crySimpProp q of
                    PTrue  -> p'
                    PFalse -> PFalse
                    q'     -> p' :&& q'

    p :|| q ->
      case crySimpProp p of
        PTrue  -> PTrue
        PFalse -> crySimpProp q
        p'     -> case crySimpProp q of
                    PTrue  -> PTrue
                    PFalse -> p'
                    q'     -> p' :|| q'

    Not p -> crySimpProp (cryNot p)

    Fin (Var _) -> prop
    Fin p       -> crySimpProp (cryIsFin p)

    _     -> prop




-- | Generate a property ensuring that the expression is well-defined.
-- This might be a bit too strict.  For example, we reject things like
-- @max inf (0 - 1)@, which one might think would simplify to @inf@.
cryDefined :: Expr -> Prop
cryDefined expr =
  case expr of
    K _   -> PTrue
    Var _ -> PTrue    -- Variables are always assumed to be OK.
                      -- The idea is that we are going to check for
                      -- defined-ness before instantiating variables.
    x :+ y    -> cryDefined x :&& cryDefined y
    x :- y    -> cryDefined x :&& cryDefined y :&&
                 cryIsFin y :&& cryIsGeq x y
    x :* y    -> cryDefined x :&& cryDefined y
    Div x y   -> cryDefined x :&& cryDefined y :&&
                 cryIsFin x :&& cryNot0 y
    Mod x y   -> cryDefined x :&& cryDefined y :&&
                 cryIsFin x :&& cryNot0
    x :^^ y   -> cryDefined x :&& cryDefined y
    Min x y   -> cryDefined x :&& cryDefined y
    Max x y   -> cryDefined x :&& cryDefined y
    Lg2 x     -> cryDefined x
    Width x   -> cryDefined x
    LenFromThen x y w ->
      cryDefined x :&& cryDefined y :&& cryDefined w :&&
      cryIsFin x :&& cryIsFin y :&& cryIsFin w :&& cryIsNotEq x y
    LenFromThenTo x y z ->
      cryDefined x :&& cryDefined y :&& cryDefined z :&&
      cryIsFin x :&& cryIsFin y :&& cryIsFin z :&& cryIsNotEq x y




-- | Negation.
cryNot :: Prop -> Prop
cryNot prop =
  case prop of
    Fin x     -> cryIsInf x
    x :== y   -> cryIsNotEq x y
    x :/= y   -> cryIsEq 
    x :>= y   -> y :>  x
    x :>  y   -> y :>= x
    p :&& q   -> cryNot p :|| cryNot q
    p :|| q   -> cryNot p :&& cryNot q
    Not p     -> p
    PFalse    -> PTrue
    PTrue     -> PFalse


cryIsEq :: Expr -> Expr -> Prop
cryIsEq (K m) (K n) = if m == n then PTrue else PFalse
cryIsEq x y = (cryIsInf x :&& cryIsInf y) :||
              (cryIsFin x :&& cryIsFin y :&& x :== y)

cryIsNotEq :: Expr -> Expr -> Prop
cryIsNotEq x y = cryNot (cryIsEq x y)

cryIsGt :: Expr -> Expr -> Prop
cryIsGt x y = cryIsFin y :&& (cryIsInf x :|| (cryIsFin x :&& x :> y))

-- | Simpligy @t1 >= t2@
cryIsGeq :: Expr -> Expr -> Prop
cryIsGeq e1 e2 = cryIsEq e1 e2 :|| cryIsGt e1 e2

-- | Simplify @t == Inf@
cryIsInf :: Expr -> Prop
cryIsInf e = cryNot (cryIsFin e)

-- | Simplify a @fin@ constraint into finitness constraints on equalities
-- and some additional constraints.
-- Assuming a defined input.
cryIsFin :: Expr -> Prop
cryIsFin expr =
  case expr of
    K Inf                -> PFalse
    K (Nat _)            -> PTrue
    Var x                -> Fin (Var x)
    t1 :+ t2             -> cryIsFin t1 :&& cryIsFin t2
    t1 :- _              -> cryIsFin t1
    t1 :* t2             -> cryIsFin t1 :&& cryIsFin t2 :||
                            (cryIs0 t1 :&& cryIsInf t2) :||
                            (cryIs0 t2 :&& cryIsInf t1)

    Div t1 _             -> cryIsFin t1
    Mod _ _              -> PTrue
    t1 :^^ t2            ->
      cryIsFin t1 :&& cryIsFin t2 :||
      cryIsInf t1 :&& cryIs0 t2   :||   -- inf ^ 0
      cryIsInf t2 :&& (cryIs0 t1 :|| t1 :== K (Nat 1))
      -- 0 ^ inf, 1 ^ inf

    Min t1 t2            -> cryIsFin t1 :|| cryIsFin t2

    Max t1 t2            -> cryIsFin t1 :&& cryIsFin t2
    Lg2 t1               -> cryIsFin t1
    Width t1             -> cryIsFin t1
    LenFromThen  _ _ _   -> PTrue
    LenFromThenTo  _ _ _ -> PTrue


-- | Simplify @t == 0@.
cryIs0 :: Expr -> Prop
cryIs0 ty =
  case ty of
    K Inf               -> PFalse
    K (Nat x)           -> if x == 0 then PTrue else PFalse
    Var x               -> Var x :== K (Nat 0)
    t1 :+ t2            -> cryIs0 t1 :&& cryIs0 t2
    t1 :- t2            -> t1 :== t2
    t1 :* t2            -> cryIs0 t1 :|| cryIs0 t2
    Div t1 t2           -> (t2 :> t1)
    Mod _ _             -> ty :== K (Nat 0) -- or: t2 `Divides` t1
    t1 :^^ t2           -> cryIs0 t1 :&& cryNot0 t2
    Min t1 t2           -> cryIs0 t1 :|| cryIs0 t2
    Max t1 t2           -> cryIs0 t1 :&& cryIs0 t2
    Lg2 t1              -> cryIs0 t1 :|| (t1 :== K (Nat 1))
    Width t1            -> cryIs0 t1
    LenFromThen x y w   -> cryIs0 w :|| (x :> y)

    -- See `nLenFromThenTo` in 'Cryptol.TypeCheck.Solver.InfNat'
    LenFromThenTo x y z -> (x :> y :&& z :> x) :||
                           (y :> x :&& x :> z)


-- | Simplify @t > 0@ or @t /= 0@.
cryNot0 :: Expr -> Prop
cryNot0 ty = cryNot (cryIs0 ty)




--------------------------------------------------------------------------------

ppProp :: Prop -> Doc
ppProp = ppPropPrec 0

-- | Pretty print a proposition, in the given precedence context.
ppPropPrec :: Int -> Prop -> Doc
ppPropPrec prec prop =
  case prop of
    Fin x     -> fun "fin" ppExprPrec x
    x :== y   -> bin "==" 4 1 1 ppExprPrec x y
    x :/= y   -> bin "/=" 4 1 1 ppExprPrec x y
    x :>= y   -> bin ">=" 4 1 1 ppExprPrec x y
    x :> y    -> bin ">"  4 1 1 ppExprPrec x y
    p :&& q   -> bin "&&" 3 1 0 ppPropPrec p q
    p :|| q   -> bin "||" 2 1 0 ppPropPrec p q
    Not p     -> fun "not" ppPropPrec p
    PTrue     -> text "True"
    PFalse    -> text "False"

  where
  wrap p d = if prec > p then parens d else d

  fun f how x = wrap 10 (text f <+> how 11 x)

  bin op opP lMod rMod how x y =
    wrap opP (sep [ how (opP + lMod) x, text op, how (opP + rMod) y ])


-- | Pretty print an expression at the top level.
ppExpr :: Expr -> Doc
ppExpr = ppExprPrec 0

-- | Pretty print an expression, in the given precedence context.
ppExprPrec :: Int -> Expr -> Doc
ppExprPrec prec expr =
  case expr of
    K Inf               -> text "inf"
    K (Nat n)           -> integer n
    Var (Name x)        -> text (names !! x)
    x :+ y              -> bin "+" 6 0 1 x y
    x :- y              -> bin "-" 6 0 1 x y
    x :* y              -> bin "*" 7 0 1 x y
    Div x y             -> fun "div" [x,y]
    Mod x y             -> fun "mod" [x,y]
    x :^^ y             -> bin "*" 8 1 0 x y
    Min x y             -> fun "min" [x,y]
    Max x y             -> fun "max" [x,y]
    Lg2 x               -> fun "lg2" [x]
    Width x             -> fun "width" [x]
    LenFromThen x y w   -> fun "lenFromThen" [x,y,w]
    LenFromThenTo x y z -> fun "lenFromThenTo" [x,y,z]

  where
  wrap p d = if prec > p then parens d else d

  fun f xs = wrap 10 (text f <+> sep (map (ppExprPrec 11) xs))

  bin op opP lMod rMod x y =
    wrap opP
      (ppExprPrec (opP + lMod) x <+> text op <+> ppExprPrec (opP + rMod) y)


-- | An infinite list of names, for pretty prinitng.
names :: [String]
names  = concatMap gen [ 0 :: Integer .. ]
  where
  gen x  = [ a : suff x | a <- [ 'a' .. 'z' ] ]

  suff 0 = ""
  suff x = show x


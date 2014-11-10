{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards #-}

{- TODO:
  * Desugar more functions (e.g., min,max in terms of ite)
  * Name non-linear terms.
-}

module Cryptol.TypeCheck.Solver.CrySAT
  ( Name, toName, fromName
  , Prop(..), Expr(..), IfExpr(..)
  , cryAnds, cryOrs
  , crySimplify, crySimplified
  , cryDefined, cryDefinedProp
  , ppProp, ppPropPrec, ppExpr, ppExprPrec, ppIfExpr, ppName
  ) where

import           Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import qualified Cryptol.TypeCheck.Solver.InfNat as IN
import           Cryptol.Utils.Panic(panic)

import qualified Control.Applicative as A
import           Data.List(unfoldr, sortBy, intersperse)
import           Data.Set ( Set )
import qualified Data.Set as Set

import           Text.PrettyPrint
import           MonadLib

test :: IO ()
test =
  do writeFile "out"
      $ unlines
      $ intersperse (replicate 80 '-')
      $ map (show . ppProp)
      $ crySimpSteps
      $ Min (a :* b) (inf :* (inf :* (c :+ d))) :== a
  where
  a : b : c : d : _ = map (Var . toName) [ 0 .. ]

  _rest = Div a b
         : Mod a (b :* inf)
         : Min (a :* b) (inf :* (inf :* (c :+ d)))
         : []


--------------------------------------------------------------------------------
data Name = UserName Int | SysName Int
            deriving (Eq,Ord)

toName :: Int -> Name
toName = UserName

fromName :: Name -> Maybe Int
fromName (UserName x) = Just x
fromName (SysName _)  = Nothing

infixr 2 :||
infixr 3 :&&
infix  4 :==, :>, :>=, :==:, :>:
infixl 6 :+, :-
infixl 7 :*
infixr 8 :^^



-- | Propopsitions, representing Cryptol's numeric constraints (and a bit more).

data Prop = -- Preidcates on natural numbers with infinity.
            -- After simplification, the expression should always be a variable.
            Fin Expr

            -- Predicates on terms featuring infinity.
            -- Eliminated during simplification.
          | Expr :== Expr
          | Expr :>= Expr | Expr :> Expr

          -- Predicate on strict natural numbers (i.e., no infinities)
          -- Should be introduced by 'cryNatOp', to eliminte 'inf'.
          | Expr :==: Expr | Expr :>: Expr

          -- Standard logical strucutre
          | Prop :&& Prop | Prop :|| Prop
          | Not Prop
          | PFalse | PTrue

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
            deriving Eq

zero :: Expr
zero = K (Nat 0)

one :: Expr
one = K (Nat 1)

inf :: Expr
inf = K Inf


-- | Compute all expressions in a property.
cryPropExprs :: Prop -> [Expr]
cryPropExprs = go []
  where
  go es prop =
    case prop of
      PTrue     -> es
      PFalse    -> es
      Not p     -> go es p
      p :&& q   -> go (go es q) p
      p :|| q   -> go (go es q) p

      Fin x     -> x : es

      x :== y   -> x : y : es
      x :>  y   -> x : y : es
      x :>= y   -> x : y : es

      x :==: y  -> x : y : es
      x :>:  y  -> x : y : es


-- | Compute the immediate sub-expressions of an expression.
cryExprExprs :: Expr -> [Expr]
cryExprExprs expr =
  case expr of
    K _                 -> []
    Var _               -> []
    x :+ y              -> [x,y]
    x :- y              -> [x,y]
    x :* y              -> [x,y]
    Div x y             -> [x,y]
    Mod x y             -> [x,y]
    x :^^ y             -> [x,y]
    Min x y             -> [x,y]
    Max x y             -> [x,y]
    Lg2 x               -> [x]
    Width x             -> [x]
    LenFromThen   x y z -> [x,y,z]
    LenFromThenTo x y z -> [x,y,z]

cryRebuildExpr :: Expr -> [Expr] -> Expr
cryRebuildExpr expr args =
  case (expr,args) of
    (K _,   [])                     -> expr
    (Var _, [])                     -> expr
    (_ :+ _k, [x,y])                -> x :+ y
    (_ :- _ , [x,y])                -> x :- y
    (_ :* _ , [x,y])                -> x :* y
    (Div _ _, [x,y])                -> Div x y
    (Mod _ _, [x,y])                -> Mod x y
    (_ :^^ _, [x,y])                -> x :^^ y
    (Min _ _, [x,y])                -> Min x y
    (Max _ _, [x,y])                -> Max x y
    (Lg2 _  , [x])                  -> Lg2 x
    (Width _, [x])                  -> Width x
    (LenFromThen   _ _ _ , [x,y,z]) -> LenFromThen x y z
    (LenFromThenTo _ _ _ , [x,y,z]) -> LenFromThenTo x y z
    _ -> panic "cryRebuildExpr" $ map show
           $ text "expr:" <+> ppExpr expr
           : [ text "arg:" <+> ppExpr a | a <- args ]




cryExprFVS :: Expr -> Set Name
cryExprFVS expr =
  case expr of
    Var x -> Set.singleton x
    _     -> Set.unions (map cryExprFVS (cryExprExprs expr))

--------------------------------------------------------------------------------


-- | Simplify a property, if possible.
-- Simplification should ensure at least the properties captrured by
-- 'crySimplified' (as long as things are 'cryDefined').
--
--  crySimplified (crySimplify x) == True
crySimplify :: Prop -> Prop
crySimplify p = last (p : crySimpSteps p)

-- | For sanity checking.
-- Makes explicit some of the invariants of simplified terms.
crySimplified :: Prop -> Bool
crySimplified = go True
  where
  go atTop prop =
    case prop of
      PTrue                     -> atTop
      PFalse                    -> atTop

      -- Also, there are propagatoin properties, but a bit hard to write.
      -- For example:  `Fin x && Not (Fin x)` should simplify to `PFalse`.
      p :&& q                   -> go False p && go False q
      p :|| q                   -> go False p && go False q

      Not (Fin (Var _))         -> True
      Not (x :>: y)             -> go False (x :>: y)
      Not _                     -> False

      _ :== _                   -> False
      _ :>  _                   -> False
      _ :>= _                   -> False

      Fin (Var _)               -> True
      Fin _                     -> False

      Var _ :>: K (Nat 0)       -> True
      _     :>: K (Nat 0)       -> False
      K _   :>: K _             -> False
      x     :>: y               -> noInf x && noInf y

      Var _     :==: K (Nat 0)  -> True
      K (Nat 0) :==: _          -> False
      K _       :==: K _        -> False
      x         :==: y          -> noInf x && noInf y

  noInf expr =
    case expr of
      K x                 -> x /= Inf
      Var _               -> True
      x :+ y              -> noInf2 x y
      x :- y              -> noInf2 x y
      x :* y              -> noInf2 x y
      Div x y             -> noInf2 x y
      Mod x y             -> noInf2 x y
      x :^^ y             -> noInf2 x y
      Min x y             -> noInf2 x y
      Max x y             -> noInf2 x y
      Lg2 x               -> noInf x
      Width x             -> noInf x
      LenFromThen x y w   -> noInf x && noInf y && noInf w
      LenFromThenTo x y z -> noInf x && noInf y && noInf z

  noInf2 x y = noInf x && noInf y

-- | List the simplification steps for a property.
crySimpSteps :: Prop -> [Prop]
crySimpSteps = unfoldr (fmap dup . crySimpStep)
  where dup x = (x,x)

-- | A single simplification step.
crySimpStep :: Prop -> Maybe Prop
crySimpStep prop =
  case prop of

    Fin x     -> cryIsFin x   -- Fin only on variables.

    x :== y   -> Just (cryIsEq x y)
    x :>  y   -> Just (cryIsGt x y)

    x :>= y   ->
      case (x,y) of
        (K (Nat 0), _) -> Just (y :== zero)
        (K Inf, _)     -> Just PTrue
        (_, K Inf)     -> Just (x :== inf)
        _              -> Just (x :== y :|| x :> y)

    x :==: y ->
      case (x,y) of
        (K a, K b)     -> Just (if a == b then PTrue else PFalse)
        (K (Nat 0), _) -> cryIs0 True y
        (_, K (Nat 0)) -> cryIs0 True x
        _ -> case bin (:==:) x y of
               Just p' -> Just p'
               -- Try to put variables on the RHS.
               Nothing | x == y -> Just PTrue
                       | otherwise -> case (x,y) of
                                        (Var _, _) -> Nothing
                                        (_, Var _) -> Just (y :==: x)
                                        _          -> Nothing

    x :>: y ->
      case (x,y) of
        (K (Nat 0),_)   -> Just PFalse
        (K (Nat 1),_)   -> cryIs0 True y
        (_, K (Nat 0))  -> cryGt0 True x
        _               -> case bin (:>:) x y of
                             Just p' -> Just p'
                             Nothing | x == y    -> Just PFalse
                                     | otherwise -> Nothing

    p :&& q ->
      case cryRearrangeAnd prop of
        Just prop' -> Just prop'
        Nothing ->
          case cryAnd p q of
            Just r  -> Just r
            Nothing ->
              case crySimpStep p of
                Just p' -> Just (p' :&& q)
                Nothing ->
                  case crySimpStep q of
                    Just q' -> Just (p :&& q')
                    Nothing -> Nothing

    p :|| q ->
      case cryRearrangeOr prop of
        Just prop' -> Just prop'
        Nothing ->
          case cryOr p q of
            Just r  -> Just r
            Nothing ->
              case crySimpStep p of
                Just p' -> Just (p' :|| q)
                Nothing ->
                  case crySimpStep q of
                    Just q' -> Just (p :|| q')
                    Nothing -> Nothing

    Not p -> case cryNot p of
               Just r -> Just r
               Nothing ->
                 case crySimpStep p of
                   Just p' -> Just (Not p')
                   Nothing -> Nothing

    PFalse  -> Nothing
    PTrue   -> Nothing

  where
  bin op x y =
    case crySimpExpr x of
      Just x' -> Just (op x' y)
      _ -> case crySimpExpr y of
             Just y' -> Just (op x y')
             Nothing -> Nothing


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





-- | Make a conjucntion of the given properties.
-- Does not perform simplification.
cryAnds :: [Prop] -> Prop
cryAnds []       = PTrue
cryAnds [p]      = p
cryAnds (p : qs) = p :&& cryAnds qs

cryOrs :: [Prop] -> Prop
cryOrs []        = PFalse
cryOrs [p]       = p
cryOrs (p : qs)  = p :|| cryOrs qs


-- | Identify propositions that are suiatable for inlining.
cryIsDefn :: Prop -> Maybe (Name, Expr)
cryIsDefn (Var x :==: e) = if (x `Set.member` cryExprFVS e)
                              then Nothing
                              else Just (x,e)
cryIsDefn _              = Nothing



{- | Apply the function to all elements in the list.
Return 'Nothing' if all results were 'Nothing', otherwise it
returns @Just answerws@, where each @answer@ is either the original
value (if the function gave 'Nothing'), or the result of the function. -}
anyJust :: (a -> Maybe a) -> [a] -> Maybe [a]
anyJust _ []       = Nothing
anyJust f (x : xs) = case (f x, anyJust f xs) of
                       (Nothing, Nothing)   -> Nothing
                       (Just x', Nothing)   -> Just (x' : xs)
                       (Nothing, Just xs')  -> Just (x  : xs')
                       (Just x', Just xs')  -> Just (x' : xs')


-- | Replaces occurances of the name with the expression.
-- Returns 'Nothing' if there were no occurances of the name.
class CryLet ast where
  cryLet :: Name -> Expr -> ast -> Maybe ast

instance CryLet Expr where
  cryLet a e = go
    where
    go expr =
      case expr of
        K _                 -> Nothing
        Var b               -> if a == b then Just e else Nothing
        x :+ y              -> two (:+) x y
        x :- y              -> two (:-) x y
        x :* y              -> two (:*) x y
        x :^^ y             -> two (:^^) x y
        Div x y             -> two Div x y
        Mod x y             -> two Mod x y
        Min x y             -> two Min x y
        Max x y             -> two Max x y
        Lg2 x               -> Lg2 `fmap` go x
        Width x             -> Width `fmap` go x
        LenFromThen x y w   -> three LenFromThen x y w
        LenFromThenTo x y z -> three LenFromThen x y z

    two f x y = do [x',y'] <- anyJust go [x,y]
                   return (f x' y')

    three f x y z = do [x',y',z'] <- anyJust go [x,y,z]
                       return (f x' y' z')

instance CryLet Prop where
  cryLet a e = go
    where
    go prop =
      case prop of
        PFalse    -> Nothing
        PTrue     -> Nothing
        Not p     -> Not `fmap` go p
        p :&& q   -> two (:&&) p q
        p :|| q   -> two (:||) p q
        Fin x     -> Fin `fmap` cryLet a e x
        x :== y   -> twoE (:==) x y
        x :>= y   -> twoE (:>=) x y
        x :> y    -> twoE (:>) x y
        x :==: y  -> twoE (:==:) x y
        x :>: y   -> twoE (:>) x y

    two f x y = do [x',y'] <- anyJust go [x,y]
                   return (f x' y')

    twoE f x y = do [x',y'] <- anyJust (cryLet a e) [x,y]
                    return (f x' y')


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



-- | A condition ensure that the given *basic* proposition makes sense.
cryDefinedProp :: Prop -> Prop
cryDefinedProp prop =
  case prop of
    Fin x   -> cryDefined x
    x :== y -> cryDefined x :&& cryDefined y
    x :>= y -> cryDefined x :&& cryDefined y
    _ -> panic "cryDefinedProp" [ "Not a simple property:"
                                , show (ppProp prop)
                                ]


-- | Generate a property ensuring that the expression is well-defined.
-- This might be a bit too strict.  For example, we reject things like
-- @max inf (0 - 1)@, which one might think would simplify to @inf@.
cryDefined :: Expr -> Prop
cryDefined expr =
  case expr of
    K _       -> PTrue
    Var _     -> PTrue    -- Variables are always assumed to be OK.
                      -- The idea is that we are going to check for
                      -- defined-ness before instantiating variables.
    x :+ y    -> cryDefined x :&& cryDefined y
    x :- y    -> cryDefined x :&& cryDefined y :&&
                 Fin y :&& x :>= y
    x :* y    -> cryDefined x :&& cryDefined y
    Div x y   -> cryDefined x :&& cryDefined y :&&
                 Fin x :&& Not (y :== zero)
    Mod x y   -> cryDefined x :&& cryDefined y :&&
                 Fin x :&& Not (y :== zero)
    x :^^ y   -> cryDefined x :&& cryDefined y
    Min x y   -> cryDefined x :&& cryDefined y
    Max x y   -> cryDefined x :&& cryDefined y
    Lg2 x     -> cryDefined x
    Width x   -> cryDefined x
    LenFromThen x y w ->
      cryDefined x :&& cryDefined y :&& cryDefined w :&&
      Fin x :&& Fin y :&& Fin w :&& Not (x :== y) :&& w :>= Width x
    LenFromThenTo x y z ->
      cryDefined x :&& cryDefined y :&& cryDefined z :&&
      Fin x :&& Fin y :&& Fin z :&& Not (x :== y)


-- | Simplificaiton for @:==@
cryIsEq :: Expr -> Expr -> Prop
cryIsEq x y =
  case (x,y) of
    (K m, K n)      -> if m == n then PTrue else PFalse
    (K (Nat 0),_)   -> cryIs0' y
    (_, K (Nat 0))  -> cryIs0' x

    (K Inf, _)      -> Not (Fin y)
    (_, K Inf)      -> Not (Fin x)
    _ -> case crySimpExpr x of
           Just x' -> x' :== y
           Nothing ->
             case crySimpExpr y of
               Just y' -> x :== y'
               Nothing ->
                      Not (Fin x) :&& Not (Fin y)
                  :|| Fin x :&& Fin y :&& cryNatOp (:==:) x y

  where
  cryIs0' e = case cryIs0 False e of
                Just e' -> e'
                Nothing -> panic "cryIsEq"
                                 ["`cryIs0 False` returned `Nothing`."]


-- | Simplificatoin for @:>@
cryIsGt :: Expr -> Expr -> Prop
cryIsGt (K m) (K n)   = if m > n then PTrue else PFalse
cryIsGt (K (Nat 0)) _ = PFalse
cryIsGt (K (Nat 1)) e = e :== one
cryIsGt e (K (Nat 0)) = case cryGt0 False e of
                          Just e' -> e'
                          Nothing -> panic "cryIsGt"
                                           ["`cryGt0 False` return `Nothing`"]
cryIsGt x y           =
  case crySimpExpr x of
    Just x' -> x' :> y
    Nothing -> case crySimpExpr y of
                 Just y' -> x :> y'
                 Nothing -> Fin y :&& (x :== inf :||
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
                           -- 0 ^^ inf,                  1 ^^ inf
           )

    Min t1 t2            -> Just (Fin t1 :|| Fin t2)
    Max t1 t2            -> Just (Fin t1 :&& Fin t2)
    Lg2 t1               -> Just (Fin t1)
    Width t1             -> Just (Fin t1)
    LenFromThen  _ _ _   -> Just PTrue
    LenFromThenTo  _ _ _ -> Just PTrue


-- | Simplify @t :== 0@ or @t :==: 0@.
-- Assumes defined input.
cryIs0 :: Bool -> Expr -> Maybe Prop
cryIs0 useFinite expr =
  case expr of
    K Inf               -> Just PFalse
    K (Nat n)           -> Just (if n == 0 then PTrue else PFalse)
    Var _ | useFinite   -> Nothing
          | otherwise   -> Just (Fin expr :&& expr :==: zero)
    t1 :+ t2            -> Just (eq t1 zero :&& eq t2 zero)
    t1 :- t2            -> Just (eq t1 t2)
    t1 :* t2            -> Just (eq t1 zero :|| eq t2 zero)
    Div t1 t2           -> Just (gt t2 t1)
    Mod _ _ | useFinite -> (:==: zero) `fmap` crySimpExpr expr
            | otherwise -> Just (cryNatOp (:==:) expr zero)
            -- or: Just (t2 `Divides` t1)
    t1 :^^ t2           -> Just (eq t1 zero :&& gt t2 zero)
    Min t1 t2           -> Just (eq t1 zero :|| eq t2 zero)
    Max t1 t2           -> Just (eq t1 zero :&& eq t2 zero)
    Lg2 t1              -> Just (eq t1 zero :|| eq t1 one)
    Width t1            -> Just (eq t1 zero)
    LenFromThen x y w   -> Just (eq w zero :|| gt x y)

    -- See `nLenFromThenTo` in 'Cryptol.TypeCheck.Solver.InfNat'
    LenFromThenTo x y z -> Just ( gt x y :&& gt z x
                              :|| gt y x :&& gt x z
                                )

  where
  eq x y = if useFinite then x :==: y else x :== y
  gt x y = if useFinite then x :>: y  else x :>  y


-- | Simplify @t :> 0@ or @t :>: 0@.
cryGt0 :: Bool -> Expr -> Maybe Prop
cryGt0 useFinite expr =
  case expr of
    K x                 -> Just (if x > Nat 0 then PTrue else PFalse)
    Var _ | useFinite   -> Nothing
          | otherwise   -> Just (Not (Fin expr) :||
                                 Fin expr :&& cryNatOp (:>:) expr zero)
    x :+ y              -> Just (gt x zero :|| gt y zero)
    x :- y              -> Just (gt x y)
    x :* y              -> Just (gt x zero :&& gt y zero)
    Div x y             -> Just (gt x y)
    Mod _ _ | useFinite -> (:>: zero) `fmap` crySimpExpr expr
            | otherwise -> Just (cryNatOp (:>:) expr zero)
            -- or: Just (Not (y `Divides` x))
    x :^^ y             -> Just (eq x zero :&& gt y zero)
    Min x y             -> Just (gt x zero :&& gt y zero)
    Max x y             -> Just (gt x zero :|| gt y zero)
    Lg2 x               -> Just (gt x one)
    Width x             -> Just (gt x zero)
    LenFromThen _ _ _   -> Just PTrue
    LenFromThenTo x y z -> Just (gt x y :&& gt z x :|| gt y x :&& gt x z)

  where
  eq x y = if useFinite then x :==: y else x :== y
  gt x y = if useFinite then x :>: y  else x :>  y


--------------------------------------------------------------------------------
-- Simplification of expressions
--------------------------------------------------------------------------------


-- | Make a simplification step, assuming the expression is well-formed.
crySimpExpr :: Expr -> Maybe Expr
crySimpExpr expr =
  case expr of
    K _                   -> Nothing
    Var _                 -> Nothing

    x :+ y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just y
        (K Inf, _)        -> Just inf
        (_, K (Nat 0))    -> Just x
        (_, K Inf)        -> Just inf
        (K a, K b)        -> Just (K (IN.nAdd a b))
        _                 -> bin (:+) x y

    x :- y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (K Inf, _)        -> Just inf
        (_, K (Nat 0))    -> Just x
        (K a, K b)        -> K `fmap` IN.nSub a b
        _ | x == y        -> Just zero
        _                 -> bin (:-) x y

    x :* y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (K (Nat 1), _)    -> Just y
        (_, K (Nat 0))    -> Just zero
        (_, K (Nat 1))    -> Just x
        (K a, K b)        -> Just (K (IN.nMul a b))
        _                 -> bin (:*) x y

    Div x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (_, K (Nat 1))    -> Just x
        (_, K Inf)        -> Just zero
        (K a, K b)        -> K `fmap` IN.nDiv a b
        _ | x == y        -> Just one
        _                 -> bin Div x y

    Mod x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (_, K Inf)        -> Just x
        (_, K (Nat 1))    -> Just zero
        (K a, K b)        -> K `fmap` IN.nMod a b
        _                 -> bin Mod x y

    x :^^ y ->
      case (x,y) of
        (_, K (Nat 0))    -> Just one
        (_, K (Nat 1))    -> Just x
        (K (Nat 1), _)    -> Just one
        (K a, K b)        -> Just (K (IN.nExp a b))
        _                 -> bin (:^^) x y

    Min x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (K Inf, _)        -> Just y
        (_, K (Nat 0))    -> Just zero
        (_, K Inf)        -> Just x
        (K a, K b)        -> Just (K (IN.nMin a b))
        _ | x == y        -> Just x
        _                 -> bin Min x y

    Max x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just y
        (K Inf, _)        -> Just inf
        (_, K (Nat 0))    -> Just x
        (_, K Inf)        -> Just inf
        _ | x == y        -> Just x
        _                 -> bin Max x y

    Lg2 x ->
      case x of
        K a               -> Just (K (IN.nLg2 a))
        _                 -> Lg2 `fmap` crySimpExpr x

    Width x               -> Just (Lg2 (x :+ one))

    LenFromThen x y w ->
      case (x,y,w) of
        (K a, K b, K c)   -> K `fmap` IN.nLenFromThen a b c
        _                 -> three LenFromThen x y w

    LenFromThenTo x y z ->
      case (x,y,z) of
        (K a, K b, K c)   -> K `fmap` IN.nLenFromThenTo a b c
        _                 -> three LenFromThenTo x y z

  where

  bin op x y = case crySimpExpr x of
                 Just x' -> Just (op x' y)
                 Nothing -> case crySimpExpr y of
                              Just y' -> Just (op x y')
                              Nothing -> Nothing

  three op x y z =
    case crySimpExpr x of
      Just x' -> Just (op x' y z)
      Nothing ->
        case crySimpExpr y of
          Just y' -> Just (op x y' z)
          Nothing ->
            case crySimpExpr z of
              Just z' -> Just (op x y z')
              Nothing -> Nothing







--------------------------------------------------------------------------------
-- Eliminating the @inf@ constant form finite terms.
--------------------------------------------------------------------------------


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



data IfExpr a = If Prop (IfExpr a) (IfExpr a) | Return a | Impossible

instance Functor       IfExpr where fmap = liftM
instance A.Applicative IfExpr where pure = return; (<*>) = ap
instance Monad IfExpr where
  return  = Return
  fail _  = Impossible
  m >>= k = case m of
              Impossible -> Impossible
              Return a   -> k a
              If p t e   -> If p (t >>= k) (e >>= k)


ppIfExpr :: IfExpr Expr -> Doc
ppIfExpr expr =
  case expr of
    If p t e -> hang (text "if" <+> ppProp p) 2
              ( (text "then" <+> ppIfExpr t)  $$
                (text "else" <+> ppIfExpr e)
              )
    Return e    -> ppExpr e
    Impossible  -> text "<impossible>"



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

    Lg2 x ->
      do x' <- cryNoInf x
         case x' of
           K Inf     -> return inf
           _         -> return (Lg2 x')

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



--------------------------------------------------------------------------------
-- Separate Non-Linear Constraints
--------------------------------------------------------------------------------

isNonLinOp :: Expr -> Bool
isNonLinOp expr =
  case expr of
    K _   -> False
    Var _ -> False

    _ :+ _ -> False

    _ :- _ -> False

    x :* y ->
      case (x,y) of
        (K _, _)  -> False
        (_, K _)  -> False
        _         -> True

    Div _ y ->
      case y of
        K _       -> False
        _         -> True

    Mod _ y ->
      case y of
        K _       -> False
        _         -> True

    _ :^^ _       -> True

    Min _ _       -> False

    Max _ _       -> False

    Lg2 _         -> True

    Width _       -> True

    LenFromThen _ _ _ -> False -- See also comment on `LenFromThenTo`

    LenFromThenTo x y _ ->
      case (x,y) of
        (K _, K _) -> False
        _          -> True    -- Actually, as long as the difference bettwen
                              -- `x` and `y` is constant we'd be OK, but not
                              -- sure how to do that...


-- | Factor-out non-linear terms, by naming them
nonLin :: Expr -> ([(Name,Expr)], Expr)
nonLin expr = case runId $ runStateT s0 $ nonLinM expr of
                (e, sFin) -> (nonLinExprs sFin, e)
  where
  s0 = NonLinS { nextName = 0, nonLinExprs = [] }

nonLinM :: Expr -> NonLinM Expr
nonLinM expr
  | isNonLinOp expr = nameExpr expr
  | otherwise = cryRebuildExpr expr `fmap` mapM nonLinM (cryExprExprs expr)



type NonLinM = StateT NonLinS Id

data NonLinS = NonLinS
  { nextName    :: !Int
  , nonLinExprs :: [(Name,Expr)]
  }

nameExpr :: Expr -> NonLinM Expr
nameExpr e = sets $ \s -> let x  = nextName s
                              n  = SysName x
                              s1 = NonLinS { nextName = 1 + x
                                           , nonLinExprs = (n,e) : nonLinExprs s
                                           }
                          in s1 `seq` (Var n, s1)


--------------------------------------------------------------------------------
-- Desugar into SMTLIB Terminology
--------------------------------------------------------------------------------

-- XXX: Expanding the if-then-elses could make things large.
-- Perhaps keep them as first class things, in hope that the solver
-- can do something more clever with that?


-- | Assumes simplified, linear, finite, defined expressions.
desugarExpr :: Expr -> IfExpr Expr
desugarExpr expr =
  do es <- mapM desugarExpr (cryExprExprs expr)
     case (expr,es) of
       (Min {}, [x,y]) -> If (x :>: y) (return y) (return x)
       (Max {}, [x,y]) -> If (x :>: y) (return x) (return y)
       (LenFromThenTo {}, [ x@(K (Nat a)), K (Nat b), z ])
          | a > b -> If (z :>: x) (return zero)
                                  (return (Div (z :- x) step :+ one))
          | b < a -> If (x :>: z) (return zero)
                                  (return (Div (x :- z) step :+ one))

          where step = K (Nat (abs (a - b)))

       _ -> return (cryRebuildExpr expr es)


-- Assumes simplified, linear, defined.
desugarProp :: Prop -> IfExpr Prop
desugarProp prop =
  case prop of
    PFalse      -> return PFalse
    PTrue       -> return PTrue
    Not p       -> Not   `fmap` desugarProp p
    p :&& q     -> (:&&) `fmap` desugarProp p `ap` desugarProp q
    p :|| q     -> (:||) `fmap` desugarProp p `ap` desugarProp q
    Fin (Var _) -> return prop
    Fin _       -> unexpected
    x :==: y    -> (:==:) `fmap` desugarExpr x `ap` desugarExpr y
    x :>: y     -> (:>:)  `fmap` desugarExpr x `ap` desugarExpr y

    _ :== _   -> unexpected
    _ :>= _   -> unexpected
    _ :> _    -> unexpected

  where
  unexpected = panic "desugarProp" [ show (ppProp prop) ]


ifPropToSmtLib :: IfExpr Prop -> Doc
ifPropToSmtLib ifProp =
  case ifProp of
    Impossible -> smtFun "false" []     -- Sholdn't really matter
    Return p   -> propToSmtLib p
    If p q r   -> smtFun "ite" [ propToSmtLib p
                               , ifPropToSmtLib q, ifPropToSmtLib r ]

propToSmtLib :: Prop -> Doc
propToSmtLib prop =
  case prop of
    PFalse      -> smtFun "false" []
    PTrue       -> smtFun "true" []
    Not p       -> smtFun "not" [ propToSmtLib p ]
    p :&& q     -> smtFun "and" [ propToSmtLib p, propToSmtLib q ]
    p :|| q     -> smtFun "or"  [ propToSmtLib p, propToSmtLib q ]
    Fin (Var x) -> smtFun ("fin_" ++ show (ppName x)) []
    x :==: y    -> smtFun "="  [ exprToSmtLib x, exprToSmtLib y ]
    x :>: y     -> smtFun ">"  [ exprToSmtLib x, exprToSmtLib y ]

    Fin _       -> unexpected
    _ :== _     -> unexpected
    _ :>= _     -> unexpected
    _ :> _      -> unexpected

  where
  unexpected = panic "desugarProp" [ show (ppProp prop) ]



ifExprToSmtLib :: IfExpr Expr -> Doc
ifExprToSmtLib ifExpr =
  case ifExpr of
    Impossible  -> integer 0xDEADBEEF -- Shouldn't really matter
    Return e    -> exprToSmtLib e
    If p x y    -> smtFun "ite" [ propToSmtLib p
                                , ifExprToSmtLib x, ifExprToSmtLib y ]

exprToSmtLib :: Expr -> Doc
exprToSmtLib expr =

  case expr of
    K (Nat n)           -> integer n
    K Inf               -> unexpected
    Var a               -> ppName a
    x :+ y              -> fun "+" [x,y]
    x :- y              -> fun "-" [x,y]
    x :* y              -> fun "*" [x,y]
    Div x y             -> fun "div" [x,y]
    Mod x y             -> fun "mod" [x,y]
    _ :^^ _             -> unexpected
    Min {}              -> unexpected
    Max {}              -> unexpected
    Lg2 {}              -> unexpected
    Width {}            -> unexpected
    LenFromThen {}      -> unexpected
    LenFromThenTo {}    -> unexpected

  where
  fun x xs   = smtFun x (map exprToSmtLib xs)
  unexpected = panic "exprToSmtLib" [ show (ppExpr expr) ]

smtFun :: String -> [Doc] -> Doc
smtFun f xs = parens $ sep (text f : xs)


--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

-- | Pretty print a top-level property.
ppProp :: Prop -> Doc
ppProp = ppPropPrec 0

-- | Pretty print a proposition, in the given precedence context.
ppPropPrec :: Int -> Prop -> Doc
ppPropPrec prec prop =
  case prop of
    Fin x     -> fun "fin" ppExprPrec x
    x :== y   -> bin "==" 4 1 1 ppExprPrec x y
    x :>= y   -> bin ">=" 4 1 1 ppExprPrec x y
    x :> y    -> bin ">"  4 1 1 ppExprPrec x y

    x :==: y  -> bin "==#" 4 1 1 ppExprPrec x y
    x :>: y   -> bin ">#"  4 1 1 ppExprPrec x y

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
    Var a               -> ppName a
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

ppName :: Name -> Doc
ppName name =
  case name of
    UserName x -> text (names !! x)
    SysName  x -> char '_' <> text (names !! x)

-- | An infinite list of names, for pretty prinitng.
names :: [String]
names  = concatMap gen [ 0 :: Integer .. ]
  where
  gen x  = [ a : suff x | a <- [ 'a' .. 'z' ] ]

  suff 0 = ""
  suff x = show x


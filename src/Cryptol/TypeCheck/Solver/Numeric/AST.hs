{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
-- | The sytnax of numeric propositions.
module Cryptol.TypeCheck.Solver.Numeric.AST
  ( Name, toName, sysName, fromName, ppName

  , Prop(..), cryPropExprs, cryPropFVS
  , ppProp, ppPropPrec

  , Expr(..), zero, one, inf, cryAnds, cryOrs
  , cryExprExprs, cryRebuildExpr
  , cryExprFVS
  , ppExpr, ppExprPrec

  , Nat'(..)

  , IfExpr(..), ppIfExpr

  , Subst, HasVars(..), cryLet
  ) where

import          Cryptol.TypeCheck.Solver.InfNat ( Nat'(..) )
import          Cryptol.Utils.Panic ( panic )
import          Cryptol.Utils.Misc ( anyJust )

import           Data.GenericTrie (TrieKey)
import           GHC.Generics(Generic)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set
import qualified Control.Applicative as A
import           Control.Monad ( liftM, ap )
import           Text.PrettyPrint ( Doc, text, (<+>), hang, ($$), char, (<>)
                                  , parens, integer, sep )


infixr 2 :||
infixr 3 :&&
infix  4 :==, :>, :>=, :==:, :>:
infixl 6 :+, :-
infixl 7 :*
infixr 8 :^^



data Name = UserName Int | SysName Int
            deriving (Show,Eq,Ord,Generic)

toName :: Int -> Name
toName = UserName

sysName :: Int -> Name
sysName = SysName

fromName :: Name -> Maybe Int
fromName (UserName x) = Just x
fromName (SysName _)  = Nothing



-- | Propopsitions, representing Cryptol's numeric constraints (and a bit more).
data Prop =

   -- Preidcates on natural numbers with infinity.
   -- After simplification, the only one of these should be `fin x`,
   -- where `x` is a variable.

   Fin Expr | Expr :== Expr | Expr :>= Expr | Expr :> Expr


  -- Predicate on strict natural numbers (i.e., no infinities)
  -- Should be introduced by 'cryNatOp', to eliminte 'inf'.
  | Expr :==: Expr | Expr :>: Expr

  -- Standard logical strucutre>
  | Prop :&& Prop | Prop :|| Prop
  | Not Prop
  | PFalse | PTrue
    deriving (Eq,Show,Generic)


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
            deriving (Eq,Show,Generic)


-- | The constant @0@.
zero :: Expr
zero = K (Nat 0)

-- | The constant @1@.
one :: Expr
one = K (Nat 1)

-- | The constant @infinity@.
inf :: Expr
inf = K Inf


-- | Make a conjucntion of the given properties.
cryAnds :: [Prop] -> Prop
cryAnds []  = PTrue
cryAnds ps  = foldr1 (:&&) ps

-- | Make a disjunction of the given properties.
cryOrs :: [Prop] -> Prop
cryOrs []   = PFalse
cryOrs ps   = foldr1 (:||) ps




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

-- | Rebuild an expression, using the top-level strucutre of the first
-- expression, but the second list of expressions as sub-expressions.
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


-- | Compute the free variables in an expression.
cryExprFVS :: Expr -> Set Name
cryExprFVS expr =
  case expr of
    Var x -> Set.singleton x
    _     -> Set.unions (map cryExprFVS (cryExprExprs expr))

-- | Compute the free variables in a proposition.
cryPropFVS :: Prop -> Set Name
cryPropFVS = Set.unions . map cryExprFVS . cryPropExprs





data IfExpr a = If Prop (IfExpr a) (IfExpr a) | Return a | Impossible

instance Monad IfExpr where
  return  = Return
  fail _  = Impossible
  m >>= k = case m of
              Impossible -> Impossible
              Return a   -> k a
              If p t e   -> If p (t >>= k) (e >>= k)

instance Functor IfExpr where
  fmap  = liftM

instance A.Applicative IfExpr where
  pure  = return
  (<*>) = ap


--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

type Subst = Map Name Expr

cryLet :: HasVars e => Name -> Expr -> e -> Maybe e
cryLet x e = apSubst (Map.singleton x e)

-- | Replaces occurances of the name with the expression.
-- Returns 'Nothing' if there were no occurances of the name.
class HasVars ast where
  apSubst :: Subst -> ast -> Maybe ast

instance HasVars Expr where
  apSubst su = go
    where
    go expr =
      case expr of
        K _                 -> Nothing
        Var b               -> Map.lookup b su
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

instance HasVars Prop where
  apSubst su = go
    where
    go prop =
      case prop of
        PFalse    -> Nothing
        PTrue     -> Nothing
        Not p     -> Not `fmap` go p
        p :&& q   -> two (:&&) p q
        p :|| q   -> two (:||) p q
        Fin x     -> Fin `fmap` apSubst su x
        x :== y   -> twoE (:==) x y
        x :>= y   -> twoE (:>=) x y
        x :> y    -> twoE (:>) x y
        x :==: y  -> twoE (:==:) x y
        x :>: y   -> twoE (:>) x y

    two f x y = do [x',y'] <- anyJust go [x,y]
                   return (f x' y')

    twoE f x y = do [x',y'] <- anyJust (apSubst su) [x,y]
                    return (f x' y')


--------------------------------------------------------------------------------
-- Tries
--------------------------------------------------------------------------------

instance TrieKey Name
instance TrieKey Prop
instance TrieKey Expr




--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

-- | Pretty print a name.
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



-- | Pretty print an experssion with ifs.
ppIfExpr :: IfExpr Expr -> Doc
ppIfExpr expr =
  case expr of
    If p t e -> hang (text "if" <+> ppProp p) 2
              ( (text "then" <+> ppIfExpr t)  $$
                (text "else" <+> ppIfExpr e)
              )
    Return e    -> ppExpr e
    Impossible  -> text "<impossible>"




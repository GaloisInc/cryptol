module Solver.Numeric.Interval where

import Cryptol.TypeCheck.Solver.Numeric.AST
import Cryptol.TypeCheck.Solver.InfNat

import Data.Maybe(fromMaybe)
import Text.PrettyPrint

data Interval = Interval
  { iLower :: Nat'          -- ^ lower bound (inclusive)
  , iUpper :: Maybe Nat'
    -- ^ upper bound (inclusinve)
    -- If there is no upper bound, than all *natural* numbers.
  }

ppInterval :: Interval -> Doc
ppInterval x = brackets (hsep [ pp (iLower x)
                              , text ".."
                              , maybe empty pp (iUpper x)])
  where
  pp a = case a of
           Nat n -> integer n
           Inf   -> text "inf"


-- | Any value
iAny :: Interval
iAny = Interval (Nat 0) (Just Inf)

-- | Any finite value
iAnyFin :: Interval
iAnyFin = Interval (Nat 0) Nothing

-- | Exactly this value
iConst :: Nat' -> Interval
iConst x = Interval x (Just x)

iAdd :: Interval -> Interval -> Interval
iAdd i j = Interval { iLower = nAdd (iLower i) (iLower j)
                    , iUpper = case (iUpper i, iUpper j) of
                                (Nothing, Nothing) -> Nothing
                                (Just x, Just y)   -> Just (nAdd x y)
                                (Nothing, Just y)  -> upper y
                                (Just x, Nothing)  -> upper x
                    }
  where
  upper x = case x of
              Inf -> Just Inf
              _   -> Nothing

iSub :: Interval -> Interval -> Maybe Interval
iSub i j =
  case iUpper i of
    Nothing -> case iLower j of
                 Nat _ -> Just Interval { iLower = l, iUpper = Nothing }
                 Inf   -> Nothing         -- subtract infinitiy
    Just n  -> do u <- nSub n (iLower j)
                  return Interval { iLower = l, iUpper = Just u }

  where l = fromMaybe (Nat 0) (nSub (iLower i) =<< iUpper j)



{-

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
-}


{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.Numeric.ImportExport
  ( ExportM
  , exportProp
  , runExportM
  , exportPropM
  , exportTypeM
  , importType
  ) where

import           Cryptol.TypeCheck.Solver.Numeric.AST
import qualified Cryptol.TypeCheck.AST as Cry
import           Data.Map ( Map )
import qualified Data.Map as Map
import           MonadLib

exportProp :: Cry.Prop -> Maybe Prop
exportProp = fmap fst . runExportM . exportPropM

runExportM :: ExportM a -> Maybe (a, VarMap)
runExportM = either (\_ -> Nothing) Just
           . runId
           . runExceptionT
           . runStateT Map.empty

type ExportM = StateT VarMap (ExceptionT () Id)
type VarMap  = Map Name Cry.TVar

exportPropM :: Cry.Prop -> ExportM Prop
exportPropM ty =
  case ty of
    Cry.TUser _ _ t -> exportPropM t
    Cry.TRec {}     -> raise ()
    Cry.TVar {}     -> raise ()
    Cry.TCon (Cry.PC pc) ts ->
      mapM exportTypeM ts >>= \ets ->
      case (pc, ets) of
        (Cry.PFin,   [t])     -> return (Fin t)
        (Cry.PEqual, [t1,t2]) -> return (t1 :== t2)
        (Cry.PNeq,   [t1,t2]) -> return (t1 :== t2)
        (Cry.PGeq,   [t1,t2]) -> return (t1 :>= t2)
        _                     -> raise ()
    Cry.TCon _ _ -> raise ()

exportTypeM :: Cry.Type -> ExportM Expr
exportTypeM ty =
  case ty of
    Cry.TUser _ _ t -> exportTypeM t
    Cry.TRec {}     -> raise ()
    Cry.TVar x      -> do let name = toName (exportVar x)
                          sets_ (Map.insert name x)
                          return (Var name)
    Cry.TCon tc ts  ->
      case tc of
        Cry.TC Cry.TCInf     -> return (K Inf)
        Cry.TC (Cry.TCNum x) -> return (K (Nat x))
        Cry.TC _             -> raise ()

        Cry.TF f ->
          mapM exportTypeM ts >>= \ets ->
          case (f, ets) of
            (Cry.TCAdd, [t1,t2]) -> return (t1 :+ t2)
            (Cry.TCSub, [t1,t2]) -> return (t1 :- t2)
            (Cry.TCMul, [t1,t2]) -> return (t1 :* t2)
            (Cry.TCDiv, [t1,t2]) -> return (Div t1 t2)
            (Cry.TCMod, [t1,t2]) -> return (Mod t1 t2)
            (Cry.TCExp, [t1,t2]) -> return (t1 :^^ t2)
            (Cry.TCMin, [t1,t2]) -> return (Min t1 t2)
            (Cry.TCMax, [t1,t2]) -> return (Max t1 t2)
            (Cry.TCLg2, [t1])    -> return (Lg2 t1)
            (Cry.TCWidth, [t1])  -> return (Width t1)
            (Cry.TCLenFromThen,   [t1,t2,t3]) -> return (LenFromThen   t1 t2 t3)
            (Cry.TCLenFromThenTo, [t1,t2,t3]) -> return (LenFromThenTo t1 t2 t3)

            _ -> raise ()

        Cry.PC _ -> raise ()


exportVar :: Cry.TVar -> Int
exportVar (Cry.TVFree x _ _ _) = 2 * x        -- Free vars are even
exportVar (Cry.TVBound x _)    = 2 * x + 1    -- Bound vars are odd


importType :: VarMap -> Expr -> Maybe Cry.Type
importType vars = go
  where
  go expr =
    case expr of
      Var x               -> Cry.TVar `fmap` Map.lookup x vars
      K n                 -> case n of
                               Nat x -> Just (Cry.tNum x)
                               Inf   -> Just (Cry.tInf)
      x :+ y              -> op2 Cry.TCAdd x y
      x :- y              -> op2 Cry.TCSub x y
      x :* y              -> op2 Cry.TCMul x y
      Div x y             -> op2 Cry.TCDiv x y
      Mod x y             -> op2 Cry.TCMod x y
      x :^^ y             -> op2 Cry.TCExp x y
      Min x y             -> op2 Cry.TCMin x y
      Max x y             -> op2 Cry.TCMax x y
      Lg2 x               -> op1 Cry.TCLg2 x
      Width x             -> op1 Cry.TCWidth x
      LenFromThen   x y z -> op3 Cry.TCLenFromThen x y z
      LenFromThenTo x y z -> op3 Cry.TCLenFromThenTo x y z

  app f xs = Cry.TCon (Cry.TF f) xs

  op1 f x =
    do t <- go x
       return (app f [t])

  op2 f x y =
    do t1 <- go x
       t2 <- go y
       return (app f [t1,t2])

  op3 f x y z =
    do t1 <- go x
       t2 <- go y
       t3 <- go z
       return (app f [t1,t2,t3])


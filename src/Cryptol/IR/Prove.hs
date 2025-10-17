module Cryptol.IR.Prove
  ( satProve,
    QueryType(..),
    SatNum(..),
    ProverResult(..),
    SatResult,
    CounterExampleType(..),
    Concrete.Value,
    TValue(..),
    GenValue(..)
  ) where

import           Data.IORef(newIORef)

import           Cryptol.Utils.Panic(panic)
import           Cryptol.TypeCheck.AST(Type,DeclGroup,Expr,tMono)
import           Cryptol.ModuleSystem.Monad(ModuleM)
import qualified Cryptol.ModuleSystem.Monad as M

import           Cryptol.Symbolic
import qualified Cryptol.Symbolic.What4 as W4
import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.Eval.Type(TValue(..))
import           Cryptol.Eval.Value(GenValue(..))


-- | Use an SMT solver to check if an expression is satisifiable
satProve ::
  [DeclGroup]   {-^ Additional definitions -} ->
  Expr          {-^ The expression we are examining -} ->
  Type          {-^ The type of the expression to examine -} ->
  Int           {-^ Timeout in seconds -} ->
  ModuleM [SatResult]
  {- ^ A list of possible models (lazy).  Empty if no models were found. -}
satProve decls expr exprType timeoutSec =
  do
    timing <- M.io (newIORef 0)
    let
      cmd =
        ProverCommand {
          pcQueryType    = SatQuery AllSat,
          pcProverName   = "z3",
          pcVerbose      = False,
          pcValidate     = True,
          pcProverStats  = timing,
          pcExtraDecls   = decls,
          pcSmtFile      = Nothing,
          pcExpr         = expr,
          pcSchema       = tMono exprType,
          pcIgnoreSafety = False
        }
    res <- snd <$> M.doModuleCmd (W4.satProve W4.defaultProver False True timeoutSec cmd)
    case res of
      AllSatResult xs   -> pure xs
      ThmResult {}      -> pure []
      CounterExample {} -> panic "satProve" ["Unexpected CounterExample"]
      EmptyResult       -> panic "satProve" ["Unexpecetd EmptyResult"]
      ProverError d     -> fail (show d)


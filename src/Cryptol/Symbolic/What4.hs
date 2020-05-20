-- |
-- Module      :  Cryptol.Symbolic.What4
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic.What4
 ( proverNames
-- , checkProverInstallation
 , satProve
 , satProveOffline
 ) where

import Control.Monad.IO.Class
import Control.Monad (when, foldM)
import qualified Data.Map as Map
import qualified Control.Exception as X
import System.IO (Handle)
import Data.Time
import Data.IORef

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Concrete.Float as Concrete

import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.What4
import qualified Cryptol.Eval.What4.SFloat as W4
import           Cryptol.Symbolic
import           Cryptol.TypeCheck.AST
import           Cryptol.Utils.Ident (Ident)
import           Cryptol.Utils.Logger(logPutStrLn)
import           Cryptol.Utils.Panic (panic)

import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.GroundEval as W4
import qualified What4.SatResult as W4
import qualified What4.SWord as SW
import           What4.Solver
import qualified What4.Solver.Adapter as W4

import           Data.Parameterized.Nonce


import Prelude ()
import Prelude.Compat

--import Data.Time (NominalDiffTime)

doEval :: MonadIO m => Eval.EvalOpts -> Eval.Eval a -> m a
doEval evo m = liftIO $ Eval.runEval evo m

doW4Eval :: (W4.IsExprBuilder sym, MonadIO m) => sym -> Eval.EvalOpts -> W4Eval sym a -> m (W4.Pred sym, a)
doW4Eval sym evo m =
  (liftIO $ Eval.runEval evo (w4Eval m sym)) >>= \case
    W4Error err -> liftIO (X.throwIO err)
    W4Result p x -> pure (p, x)

-- External interface ----------------------------------------------------------

proverConfigs :: [(String, SolverAdapter st)]
proverConfigs =
  [ ("w4-cvc4"     , cvc4Adapter )
  , ("w4-yices"    , yicesAdapter )
  , ("w4-z3"       , z3Adapter )
  , ("w4-boolector", boolectorAdapter )
  , ("w4-offline"  , z3Adapter )
{-
  , ("mathsat"  , SBV.mathSAT  )
  , ("abc"      , SBV.abc      )
  , ("any"      , SBV.defaultSMTCfg )
-}
  ]

proverNames :: [String]
proverNames = map fst proverConfigs

lookupProver :: String -> IO (SolverAdapter st)
lookupProver s =
  case lookup s proverConfigs of
   Just cfg -> pure cfg
   Nothing  -> panic "lookupProver" ["unknown solver name: " ++ s]

--checkProverInstallation :: String -> IO Bool
--checkProverInstallation _s =
--  do putStrLn "TODO! What4 check solver installation"
--     return True

proverError :: String -> M.ModuleCmd (Maybe String, ProverResult)
proverError msg (_,modEnv) =
  return (Right ((Nothing, ProverError msg), modEnv), [])


data CryptolState t = CryptolState


-- TODO? move this?
allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedNonParamModules

satProve :: ProverCommand -> M.ModuleCmd (Maybe String, ProverResult)
satProve ProverCommand {..} =
  protectStack proverError $ \(evo, modEnv) ->

  M.runModuleM (evo,modEnv) $ do
    let extDgs = allDeclGroups modEnv ++ pcExtraDecls
    let lPutStrLn = M.withLogger logPutStrLn
    primMap <- M.getPrimMap

    sym <- M.io (W4.newExprBuilder W4.FloatIEEERepr CryptolState globalNonceGenerator)

    logData <-
      flip M.withLogger () $ \lg () ->
          pure $ defaultLogData
            { logCallbackVerbose = \i msg -> when (i > 2) (logPutStrLn lg msg)
            , logReason = "solver query"
            }

    start <- liftIO $ getCurrentTime

    let ?evalPrim = evalPrim sym
    case predArgTypes pcSchema of
      Left msg -> return (Nothing, ProverError msg)
      Right ts ->
         when pcVerbose (lPutStrLn "Simulating...") >> liftIO (
         do args <- mapM (freshVariable sym) ts

            (safety,b) <-
               doW4Eval sym evo $
                   do env <- Eval.evalDecls (What4 sym) extDgs mempty
                      v <- Eval.evalExpr (What4 sym) env pcExpr
                      Eval.fromVBit <$> foldM Eval.fromVFun v (map (pure . varToSymValue sym) args)

            result <- case pcQueryType of
              ProveQuery ->
                do q <- W4.notPred sym =<< W4.andPred sym safety b
                   singleQuery sym evo primMap pcProverName logData ts args q

              SatQuery num ->
                do q <- W4.andPred sym safety b
                   multiSATQuery sym evo primMap pcProverName logData ts args q num

            end <- getCurrentTime
            writeIORef pcProverStats (diffUTCTime end start)
            return result)

satProveOffline :: ProverCommand -> ((Handle -> IO ()) -> IO ()) -> M.ModuleCmd (Maybe String)
satProveOffline ProverCommand {..} outputContinuation =
  protectStack (\msg (_,modEnv) -> return (Right (Just msg, modEnv), [])) $
  \(evo,modEnv) -> do
  M.runModuleM (evo,modEnv) $ do
    let extDgs = allDeclGroups modEnv ++ pcExtraDecls
    let lPutStrLn = M.withLogger logPutStrLn

    sym <- M.io (W4.newExprBuilder W4.FloatIEEERepr CryptolState globalNonceGenerator)

    let ?evalPrim = evalPrim sym
    case predArgTypes pcSchema of
      Left msg -> return (Just msg)
      Right ts ->
         do when pcVerbose $ lPutStrLn "Simulating..."
            liftIO $ do
              args <- mapM (freshVariable sym) ts

              (safety,b) <-
                 doW4Eval sym evo $
                     do env <- Eval.evalDecls (What4 sym) extDgs mempty
                        v <- Eval.evalExpr (What4 sym) env pcExpr
                        Eval.fromVBit <$> foldM Eval.fromVFun v (map (pure . varToSymValue sym) args)

              q <- case pcQueryType of
                ProveQuery ->
                  W4.notPred sym =<< W4.andPred sym safety b
                SatQuery _ ->
                  W4.andPred sym safety b

              let adpt = z3Adapter
              W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)
              outputContinuation (\hdl -> solver_adapter_write_smt2 adpt sym hdl [q])
              return Nothing

decSatNum :: SatNum -> SatNum
decSatNum (SomeSat n) | n > 0 = SomeSat (n-1)
decSatNum n = n


multiSATQuery ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  sym ->
  Eval.EvalOpts ->
  PrimMap ->
  String ->
  W4.LogData ->
  [FinType] ->
  [VarShape sym] ->
  W4.Pred sym ->
  SatNum ->
  IO (Maybe String, ProverResult)
multiSATQuery sym evo primMap solverName logData ts args query (SomeSat n) | n <= 1 =
  singleQuery sym evo primMap solverName logData ts args query

multiSATQuery sym evo primMap solverName logData ts args query satNum0 =
  do adpt <- lookupProver solverName
     W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)
     pres <- W4.solver_adapter_check_sat adpt sym logData [query] $ \res ->
         case res of
           W4.Unknown -> return (Left (ProverError "Solver returned UNKNOWN"))
           W4.Unsat _ -> return (Left (ThmResult (map unFinType ts)))
           W4.Sat (evalFn,_) ->
             do model <- computeModel evo primMap evalFn ts args
                blockingPred <- computeBlockingPred sym evalFn args
                return (Right (model, blockingPred))

     case pres of
       Left res -> pure (Just (solver_adapter_name adpt), res)
       Right (mdl,block) ->
         do mdls <- (mdl:) <$> computeMoreModels adpt [block,query] (decSatNum satNum0)
            return (Just (solver_adapter_name adpt), AllSatResult mdls)

  where

  computeMoreModels _adpt _qs (SomeSat n) | n <= 0 = return [] -- should never happen...
  computeMoreModels adpt qs (SomeSat n) | n <= 1 = -- final model
    W4.solver_adapter_check_sat adpt sym logData qs $ \res ->
         case res of
           W4.Unknown -> return []
           W4.Unsat _ -> return []
           W4.Sat (evalFn,_) ->
             do model <- computeModel evo primMap evalFn ts args
                return [model]

  computeMoreModels adpt qs satNum =
    do pres <- W4.solver_adapter_check_sat adpt sym logData qs $ \res ->
         case res of
           W4.Unknown -> return Nothing
           W4.Unsat _ -> return Nothing
           W4.Sat (evalFn,_) ->
             do model <- computeModel evo primMap evalFn ts args
                blockingPred <- computeBlockingPred sym evalFn args
                return (Just (model, blockingPred))

       case pres of
         Nothing -> return []
         Just (mdl, block) ->
           (mdl:) <$> computeMoreModels adpt (block:qs) (decSatNum satNum)

singleQuery ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  sym ->
  Eval.EvalOpts ->
  PrimMap ->
  String ->
  W4.LogData ->
  [FinType] ->
  [VarShape sym] ->
  W4.Pred sym ->
  IO (Maybe String, ProverResult)

--singleQuery _sym _evo _primMap "all" _logData _ts _args _query =
--  do fail "TODO portfolio solver!"

singleQuery sym evo primMap solverName logData ts args query =
  do adpt <- lookupProver solverName
     W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)
     pres <- W4.solver_adapter_check_sat adpt sym logData [query] $ \res ->
         case res of
           W4.Unknown -> return (ProverError "Solver returned UNKNOWN")
           W4.Unsat _ -> return (ThmResult (map unFinType ts))
           W4.Sat (evalFn,_) ->
             do model <- computeModel evo primMap evalFn ts args
                return (AllSatResult [ model ])

     return (Just (W4.solver_adapter_name adpt), pres)


computeBlockingPred ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  sym ->
  W4.GroundEvalFn t ->
  [VarShape sym] ->
  IO (W4.Pred sym)
computeBlockingPred sym evalFn vs =
  do ps <- mapM (varBlockingPred sym evalFn) vs
     foldM (W4.orPred sym) (W4.falsePred sym) ps

varBlockingPred ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  sym ->
  W4.GroundEvalFn t ->
  VarShape sym ->
  IO (W4.Pred sym)
varBlockingPred sym evalFn v =
  case v of
    VarBit b ->
      do blit <- W4.groundEval evalFn b
         W4.notPred sym =<< W4.eqPred sym b (W4.backendPred sym blit)
    VarInteger i ->
      do ilit <- W4.groundEval evalFn i
         W4.notPred sym =<< W4.intEq sym i =<< W4.intLit sym ilit
    VarWord SW.ZBV -> return (W4.falsePred sym)
    VarWord (SW.DBV w) ->
      do wlit <- W4.groundEval evalFn w
         W4.notPred sym =<< W4.bvEq sym w =<< W4.bvLit sym (W4.bvWidth w) wlit

    VarFloat (W4.SFloat f)
      | fr@(W4.FloatingPointPrecisionRepr e p) <- sym `W4.fpReprOf` f
      , let wid = W4.addNat e p
      , Just W4.LeqProof <- W4.isPosNat wid ->
        do bits <- W4.groundEval evalFn f
           bv   <- W4.bvLit sym wid bits
           constF <- W4.floatFromBinary sym fr bv
           -- NOTE: we are using logical equality here
           W4.notPred sym =<< W4.floatEq sym f constF
      | otherwise -> panic "varBlockingPred" [ "1 >= 2 ???" ]

    VarFinSeq _n vs -> computeBlockingPred sym evalFn vs
    VarTuple vs     -> computeBlockingPred sym evalFn vs
    VarRecord fs    -> computeBlockingPred sym evalFn (map snd (Map.toList fs))

computeModel ::
  Eval.EvalOpts ->
  PrimMap ->
  W4.GroundEvalFn t ->
  [FinType] ->
  [VarShape (W4.ExprBuilder t CryptolState fm)] ->
  IO [(Type, Expr, Concrete.Value)]
computeModel _ _ _ [] [] = return []
computeModel evo primMap evalFn (t:ts) (v:vs) =
  do v' <- varToConcreteValue evalFn v
     let t' = unFinType t
     e <- doEval evo (Concrete.toExpr primMap t' v') >>= \case
             Nothing -> panic "computeModel" ["could not compute counterexample expression"]
             Just e  -> pure e
     zs <- computeModel evo primMap evalFn ts vs
     return ((t',e,v'):zs)
computeModel _ _ _ _ _ = panic "computeModel" ["type/value list mismatch"]


data VarShape sym
  = VarBit (W4.Pred sym)
  | VarInteger (W4.SymInteger sym)
  | VarFloat (W4.SFloat sym)
  | VarWord (SW.SWord sym)
  | VarFinSeq Int [VarShape sym]
  | VarTuple [VarShape sym]
  | VarRecord (Map.Map Ident (VarShape sym))

freshVariable :: W4.IsSymExprBuilder sym => sym -> FinType -> IO (VarShape sym)
freshVariable sym ty =
  case ty of
    FTBit         -> VarBit      <$> W4.freshConstant sym W4.emptySymbol W4.BaseBoolRepr
    FTInteger     -> VarInteger  <$> W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
    FTIntMod 0    -> panic "freshVariable" ["0 modulus not allowed"]
    FTIntMod n    -> VarInteger  <$> W4.freshBoundedInt sym W4.emptySymbol (Just 0) (Just (n-1))
    FTFloat e p   -> VarFloat    <$> W4.fpFresh sym e p
    FTSeq n FTBit -> VarWord     <$> SW.freshBV sym W4.emptySymbol (toInteger n)
    FTSeq n t     -> VarFinSeq n <$> sequence (replicate n (freshVariable sym t))
    FTTuple ts    -> VarTuple    <$> mapM (freshVariable sym) ts
    FTRecord fs   -> VarRecord   <$> mapM (freshVariable sym) fs

varToSymValue :: W4.IsExprBuilder sym => sym -> VarShape sym -> Value sym
varToSymValue sym var =
  case var of
    VarBit b     -> Eval.VBit b
    VarInteger i -> Eval.VInteger i
    VarWord w    -> Eval.VWord (SW.bvWidth w) (return (Eval.WordVal w))
    VarFloat f   -> Eval.VFloat f
    VarFinSeq n vs -> Eval.VSeq (toInteger n) (Eval.finiteSeqMap (What4 sym) (map (pure . varToSymValue sym) vs))
    VarTuple vs  -> Eval.VTuple (map (pure . varToSymValue sym) vs)
    VarRecord fs -> Eval.VRecord (fmap (pure . varToSymValue sym) fs)

varToConcreteValue ::
  W4.GroundEvalFn t ->
  VarShape (W4.ExprBuilder t CryptolState fm) ->
  IO Concrete.Value
varToConcreteValue evalFn v =
  case v of
    VarBit b     -> Eval.VBit <$> W4.groundEval evalFn b
    VarInteger i -> Eval.VInteger <$> W4.groundEval evalFn i
    VarWord SW.ZBV     ->
       pure (Eval.VWord 0 (pure (Eval.WordVal (Concrete.mkBv 0 0))))
    VarWord (SW.DBV x) ->
       do let w = W4.intValue (W4.bvWidth x)
          Eval.VWord w . pure . Eval.WordVal . Concrete.mkBv w <$> W4.groundEval evalFn x
    VarFloat fv@(W4.SFloat f) ->
      do let (e,p) = W4.fpSize fv
         bits <- W4.groundEval evalFn f
         pure $ Eval.VFloat $ Concrete.floatFromBits e p bits

    VarFinSeq n vs ->
       do vs' <- mapM (varToConcreteValue evalFn) vs
          pure (Eval.VSeq (toInteger n) (Eval.finiteSeqMap Concrete.Concrete (map pure vs')))
    VarTuple vs ->
       do vs' <- mapM (varToConcreteValue evalFn) vs
          pure (Eval.VTuple (map pure vs'))
    VarRecord fs ->
       do fs' <- traverse (varToConcreteValue evalFn) fs
          pure (Eval.VRecord (fmap pure fs'))





protectStack :: (String -> M.ModuleCmd a)
             -> M.ModuleCmd a
             -> M.ModuleCmd a
protectStack mkErr cmd modEnv =
  X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg = "Symbolic evaluation failed to terminate."
        handler () = mkErr msg modEnv

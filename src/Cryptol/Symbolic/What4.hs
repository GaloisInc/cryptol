-- |
-- Module      :  Cryptol.Symbolic.What4
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic.What4
 ( W4ProverConfig
 , defaultProver
 , proverNames
 , setupProver
 , satProve
 , satProveOffline
 , W4Exception(..)
 ) where

import Control.Applicative
import Control.Concurrent.Async
import Control.Concurrent.MVar
import Control.Monad.IO.Class
import Control.Monad (when, foldM, forM_)
import qualified Control.Exception as X
import System.IO (Handle)
import Data.Time
import Data.IORef
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.List.NonEmpty as NE
import System.Exit

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M
import qualified Cryptol.ModuleSystem.Name as M

import qualified Cryptol.Backend.FloatHelpers as FH
import           Cryptol.Backend.What4
import qualified Cryptol.Backend.What4.SFloat as W4

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.What4
import           Cryptol.Symbolic
import           Cryptol.TypeCheck.AST
import           Cryptol.Utils.Logger(logPutStrLn)
import           Cryptol.Utils.Ident (preludeReferenceName, prelPrim, identText)

import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.GroundEval as W4
import qualified What4.SatResult as W4
import qualified What4.SWord as SW
import           What4.Solver
import qualified What4.Solver.Adapter as W4

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Nonce


import Prelude ()
import Prelude.Compat

data W4Exception
  = W4Ex X.SomeException
  | W4PortfolioFailure [ (Either X.SomeException (Maybe String, String)) ]

instance Show W4Exception where
  show (W4Ex e) = X.displayException e
  show (W4PortfolioFailure exs) =
       unlines ("All solveres in the portfolio failed!":map f exs)
    where
    f (Left e) = X.displayException e
    f (Right (Nothing, msg)) = msg
    f (Right (Just nm, msg)) = nm ++ ": " ++ msg

instance X.Exception W4Exception

rethrowW4Exception :: IO a -> IO a
rethrowW4Exception m = X.catchJust f m (X.throwIO . W4Ex)
  where
  f e
    | Just ( _ :: X.AsyncException) <- X.fromException e = Nothing
    | Just ( _ :: Eval.Unsupported) <- X.fromException e = Nothing
    | otherwise = Just e

protectStack :: (String -> M.ModuleCmd a)
             -> M.ModuleCmd a
             -> M.ModuleCmd a
protectStack mkErr cmd modEnv =
  rethrowW4Exception $
  X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg = "Symbolic evaluation failed to terminate."
        handler () = mkErr msg modEnv


-- | Returns definitions, together with the value and it safety predicate.
doW4Eval ::
  (W4.IsExprBuilder sym, MonadIO m) =>
  sym -> W4Eval sym a -> m (W4.Pred sym, a)
doW4Eval sym m =
  do res <- liftIO $ Eval.runEval (w4Eval m sym)
     case res of
       W4Error err  -> liftIO (X.throwIO err)
       W4Result p x -> pure (p,x)


data AnAdapter = AnAdapter (forall st. SolverAdapter st)

data W4ProverConfig
  = W4ProverConfig AnAdapter
  | W4Portfolio (NonEmpty AnAdapter)

proverConfigs :: [(String, W4ProverConfig)]
proverConfigs =
  [ ("w4-cvc4"     , W4ProverConfig (AnAdapter cvc4Adapter) )
  , ("w4-yices"    , W4ProverConfig (AnAdapter yicesAdapter) )
  , ("w4-z3"       , W4ProverConfig (AnAdapter z3Adapter) )
  , ("w4-boolector", W4ProverConfig (AnAdapter boolectorAdapter) )
  , ("w4-offline"  , W4ProverConfig (AnAdapter z3Adapter) )
  , ("w4-any"      , allSolvers)
  ]

allSolvers :: W4ProverConfig
allSolvers = W4Portfolio
  $ AnAdapter z3Adapter :|
  [ AnAdapter cvc4Adapter
  , AnAdapter boolectorAdapter
  , AnAdapter yicesAdapter
  ]

defaultProver :: W4ProverConfig
defaultProver = W4ProverConfig (AnAdapter z3Adapter)

proverNames :: [String]
proverNames = map fst proverConfigs

setupProver :: String -> IO (Either String ([String], W4ProverConfig))
setupProver nm =
  rethrowW4Exception $
  case lookup nm proverConfigs of
    Just cfg@(W4ProverConfig p) ->
      do st <- tryAdapter p
         let ws = case st of
                    Nothing -> []
                    Just ex -> [ "Warning: solver interaction failed with " ++ nm, "    " ++ show ex ]
         pure (Right (ws, cfg))

    Just (W4Portfolio ps) ->
      filterAdapters (NE.toList ps) >>= \case
         [] -> pure (Left "What4 could not communicate with any provers!")
         (p:ps') ->
           let msg = "What4 found the following solvers: " ++ show (adapterNames (p:ps')) in
           pure (Right ([msg], W4Portfolio (p:|ps')))

    Nothing -> pure (Left ("unknown solver name: " ++ nm))

  where
  adapterNames [] = []
  adapterNames (AnAdapter adpt : ps) =
    solver_adapter_name adpt : adapterNames ps

  filterAdapters [] = pure []
  filterAdapters (p:ps) =
    tryAdapter p >>= \case
      Just _err -> filterAdapters ps
      Nothing   -> (p:) <$> filterAdapters ps

  tryAdapter (AnAdapter adpt) =
     do sym <- W4.newExprBuilder W4.FloatIEEERepr CryptolState globalNonceGenerator
        W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)
        W4.smokeTest sym adpt



proverError :: String -> M.ModuleCmd (Maybe String, ProverResult)
proverError msg (_, _, modEnv) =
  return (Right ((Nothing, ProverError msg), modEnv), [])


data CryptolState t = CryptolState


setupAdapterOptions :: W4ProverConfig -> W4.ExprBuilder t CryptolState fs -> IO ()
setupAdapterOptions cfg sym =
   case cfg of
     W4ProverConfig p -> setupAnAdapter p
     W4Portfolio ps -> mapM_ setupAnAdapter ps

  where
  setupAnAdapter (AnAdapter adpt) =
    W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)


what4FreshFns :: W4.IsSymExprBuilder sym => sym -> FreshVarFns (What4 sym)
what4FreshFns sym =
  FreshVarFns
  { freshBitVar     = W4.freshConstant sym W4.emptySymbol W4.BaseBoolRepr
  , freshWordVar    = SW.freshBV sym W4.emptySymbol
  , freshIntegerVar = W4.freshBoundedInt sym W4.emptySymbol
  , freshFloatVar   = W4.fpFresh sym
  }

-- | Simulate and manipulate query into a form suitable to be sent
-- to a solver.
prepareQuery ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  ProverCommand ->
  M.ModuleT IO (Either String
                       ([FinType],[VarShape (What4 sym)],W4.Pred sym, W4.Pred sym)
               )
prepareQuery sym ProverCommand { .. } =
  case predArgTypes pcQueryType pcSchema of
    Left msg -> pure (Left msg)
    Right ts ->
      do args <- liftIO (mapM (freshVar (what4FreshFns (w4 sym))) ts)
         (safety,b) <- simulate args
         liftIO
           do -- Ignore the safety condition if the flag is set
              let safety' = if pcIgnoreSafety then W4.truePred (w4 sym) else safety

              defs <- readMVar (w4defs sym)

              Right <$>
                case pcQueryType of
                  ProveQuery ->
                    do q <- W4.notPred (w4 sym) =<< W4.andPred (w4 sym) safety' b
                       q' <- W4.andPred (w4 sym) defs q
                       pure (ts,args,safety',q')

                  SafetyQuery ->
                    do q <- W4.notPred (w4 sym) safety
                       q' <- W4.andPred (w4 sym) defs q
                       pure (ts,args,safety,q')

                  SatQuery _ ->
                    do q <- W4.andPred (w4 sym) safety' b
                       q' <- W4.andPred (w4 sym) defs q
                       pure (ts,args,safety',q')
  where
  simulate args =
    do let lPutStrLn = M.withLogger logPutStrLn
       when pcVerbose (lPutStrLn "Simulating...")

       ds <- do (_mp, m) <- M.loadModuleFrom (M.FromModule preludeReferenceName)
                let decls = mDecls m
                let nms = fst <$> Map.toList (M.ifDecls (M.ifPublic (M.genIface m)))
                let ds = Map.fromList [ (prelPrim (identText (M.nameIdent nm)), EWhere (EVar nm) decls) | nm <- nms ]
                pure ds

       let tbl = primTable sym
       let ?evalPrim = \i -> (Right <$> Map.lookup i tbl) <|>
                             (Left <$> Map.lookup i ds)

       modEnv <- M.getModuleEnv
       let extDgs = M.allDeclGroups modEnv ++ pcExtraDecls

       doW4Eval (w4 sym)
         do env <- Eval.evalDecls sym extDgs mempty
            v   <- Eval.evalExpr  sym env    pcExpr
            appliedVal <-
              foldM Eval.fromVFun v (map (pure . varShapeToValue sym) args)

            case pcQueryType of
              SafetyQuery ->
                do Eval.forceValue appliedVal
                   pure (W4.truePred (w4 sym))

              _ -> pure (Eval.fromVBit appliedVal)


satProve ::
  W4ProverConfig ->
  Bool ->
  ProverCommand ->
  M.ModuleCmd (Maybe String, ProverResult)

satProve solverCfg hashConsing ProverCommand {..} =
  protectStack proverError \(evo, byteReader, modEnv) ->
  M.runModuleM (evo, byteReader, modEnv)
  do w4sym   <- liftIO makeSym
     defVar  <- liftIO (newMVar (W4.truePred w4sym))
     let sym = What4 w4sym defVar
     logData <- M.withLogger doLog ()
     start   <- liftIO getCurrentTime
     query   <- prepareQuery sym ProverCommand { .. }
     primMap <- M.getPrimMap
     liftIO
       do result <- runProver sym logData primMap query
          end <- getCurrentTime
          writeIORef pcProverStats (diffUTCTime end start)
          return result
  where
  makeSym =
    do w4sym <- W4.newExprBuilder W4.FloatIEEERepr
                                  CryptolState
                                  globalNonceGenerator
       setupAdapterOptions solverCfg w4sym
       when hashConsing (W4.startCaching w4sym)
       pure w4sym

  doLog lg () =
    pure
    defaultLogData
      { logCallbackVerbose = \i msg -> when (i > 2) (logPutStrLn lg msg)
      , logReason = "solver query"
      }

  runProver sym logData primMap q =
    case q of
      Left msg -> pure (Nothing, ProverError msg)
      Right (ts,args,safety,query) ->
        case pcQueryType of
          ProveQuery ->
            singleQuery sym solverCfg primMap logData ts args
                                                          (Just safety) query

          SafetyQuery ->
            singleQuery sym solverCfg primMap logData ts args
                                                          (Just safety) query

          SatQuery num ->
            multiSATQuery sym solverCfg primMap logData ts args
                                                            query num



satProveOffline ::
  W4ProverConfig ->
  Bool ->
  ProverCommand ->
  ((Handle -> IO ()) -> IO ()) ->
  M.ModuleCmd (Maybe String)

satProveOffline (W4Portfolio (p:|_)) hashConsing cmd outputContinuation =
  satProveOffline (W4ProverConfig p) hashConsing cmd outputContinuation

satProveOffline (W4ProverConfig (AnAdapter adpt)) hashConsing ProverCommand {..} outputContinuation =
  protectStack onError \(evo,byteReader,modEnv) ->
  M.runModuleM (evo,byteReader,modEnv)
   do w4sym <- liftIO makeSym
      defVar  <- liftIO (newMVar (W4.truePred w4sym))
      let sym = What4 w4sym defVar
      ok  <- prepareQuery sym ProverCommand { .. }
      liftIO
        case ok of
          Left msg -> return (Just msg)
          Right (_ts,_args,_safety,query) ->
            do outputContinuation
                  (\hdl -> solver_adapter_write_smt2 adpt w4sym hdl [query])
               return Nothing
  where
  makeSym =
    do sym <- W4.newExprBuilder W4.FloatIEEERepr CryptolState
                                                    globalNonceGenerator
       W4.extendConfig (W4.solver_adapter_config_options adpt)
                       (W4.getConfiguration sym)
       when hashConsing  (W4.startCaching sym)
       pure sym

  onError msg (_,_,modEnv) = pure (Right (Just msg, modEnv), [])


decSatNum :: SatNum -> SatNum
decSatNum (SomeSat n) | n > 0 = SomeSat (n-1)
decSatNum n = n


multiSATQuery ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  What4 sym ->
  W4ProverConfig ->
  PrimMap ->
  W4.LogData ->
  [FinType] ->
  [VarShape (What4 sym)] ->
  W4.Pred sym ->
  SatNum ->
  IO (Maybe String, ProverResult)
multiSATQuery sym solverCfg primMap logData ts args query (SomeSat n) | n <= 1 =
  singleQuery sym solverCfg primMap logData ts args Nothing query

multiSATQuery _sym (W4Portfolio _) _primMap _logData _ts _args _query _satNum =
  fail "What4 portfolio solver cannot be used for multi SAT queries"

multiSATQuery sym (W4ProverConfig (AnAdapter adpt)) primMap logData ts args query satNum0 =
  do pres <- W4.solver_adapter_check_sat adpt (w4 sym) logData [query] $ \res ->
         case res of
           W4.Unknown -> return (Left (ProverError "Solver returned UNKNOWN"))
           W4.Unsat _ -> return (Left (ThmResult (map unFinType ts)))
           W4.Sat (evalFn,_) ->
             do xs <- mapM (varShapeToConcrete evalFn) args
                let model = computeModel primMap ts xs
                blockingPred <- computeBlockingPred sym args xs
                return (Right (model, blockingPred))

     case pres of
       Left res -> pure (Just (solver_adapter_name adpt), res)
       Right (mdl,block) ->
         do mdls <- (mdl:) <$> computeMoreModels [block,query] (decSatNum satNum0)
            return (Just (solver_adapter_name adpt), AllSatResult mdls)

  where

  computeMoreModels _qs (SomeSat n) | n <= 0 = return [] -- should never happen...
  computeMoreModels qs (SomeSat n) | n <= 1 = -- final model
    W4.solver_adapter_check_sat adpt (w4 sym) logData qs $ \res ->
         case res of
           W4.Unknown -> return []
           W4.Unsat _ -> return []
           W4.Sat (evalFn,_) ->
             do xs <- mapM (varShapeToConcrete evalFn) args
                let model = computeModel primMap ts xs
                return [model]

  computeMoreModels qs satNum =
    do pres <- W4.solver_adapter_check_sat adpt (w4 sym) logData qs $ \res ->
         case res of
           W4.Unknown -> return Nothing
           W4.Unsat _ -> return Nothing
           W4.Sat (evalFn,_) ->
             do xs <- mapM (varShapeToConcrete evalFn) args
                let model = computeModel primMap ts xs
                blockingPred <- computeBlockingPred sym args xs
                return (Just (model, blockingPred))

       case pres of
         Nothing -> return []
         Just (mdl, block) ->
           (mdl:) <$> computeMoreModels (block:qs) (decSatNum satNum)

singleQuery ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  What4 sym ->
  W4ProverConfig ->
  PrimMap ->
  W4.LogData ->
  [FinType] ->
  [VarShape (What4 sym)] ->
  Maybe (W4.Pred sym) {- ^ optional safety predicate.  Nothing = SAT query -} ->
  W4.Pred sym ->
  IO (Maybe String, ProverResult)

singleQuery sym (W4Portfolio ps) primMap logData ts args msafe query =
  do as <- mapM async [ singleQuery sym (W4ProverConfig p) primMap logData ts args msafe query
                      | p <- NE.toList ps
                      ]
     waitForResults [] as

 where
 waitForResults exs [] = X.throwIO (W4PortfolioFailure exs)
 waitForResults exs as =
   do (winner, result) <- waitAnyCatch as
      let others = filter (/= winner) as
      case result of
        Left ex ->
          waitForResults (Left ex:exs) others
        Right (nm, ProverError err) ->
          waitForResults (Right (nm,err) : exs) others
        Right r ->
          do forM_ others (\a -> X.throwTo (asyncThreadId a) ExitSuccess)
             return r

singleQuery sym (W4ProverConfig (AnAdapter adpt)) primMap logData ts args msafe query =
  do pres <- W4.solver_adapter_check_sat adpt (w4 sym) logData [query] $ \res ->
         case res of
           W4.Unknown -> return (ProverError "Solver returned UNKNOWN")
           W4.Unsat _ -> return (ThmResult (map unFinType ts))
           W4.Sat (evalFn,_) ->
             do xs <- mapM (varShapeToConcrete evalFn) args
                let model = computeModel primMap ts xs
                case msafe of
                  Just s ->
                    do s' <- W4.groundEval evalFn s
                       let cexType = if s' then PredicateFalsified else SafetyViolation
                       return (CounterExample cexType model)
                  Nothing -> return (AllSatResult [ model ])

     return (Just (W4.solver_adapter_name adpt), pres)


computeBlockingPred ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  What4 sym ->
  [VarShape (What4 sym)] ->
  [VarShape Concrete.Concrete] ->
  IO (W4.Pred sym)
computeBlockingPred sym vs xs =
  do res <- doW4Eval (w4 sym) (modelPred sym vs xs)
     W4.notPred (w4 sym) (snd res)

varShapeToConcrete ::
  W4.GroundEvalFn t ->
  VarShape (What4 (W4.ExprBuilder t CryptolState fm)) ->
  IO (VarShape Concrete.Concrete)
varShapeToConcrete evalFn v =
  case v of
    VarBit b -> VarBit <$> W4.groundEval evalFn b
    VarInteger i -> VarInteger <$> W4.groundEval evalFn i
    VarRational n d -> VarRational <$> W4.groundEval evalFn n <*> W4.groundEval evalFn d
    VarWord SW.ZBV -> pure (VarWord (Concrete.mkBv 0 0))
    VarWord (SW.DBV x) ->
      let w = W4.intValue (W4.bvWidth x)
       in VarWord . Concrete.mkBv w . BV.asUnsigned <$> W4.groundEval evalFn x
    VarFloat fv@(W4.SFloat f) ->
      do let (e,p) = W4.fpSize fv
         VarFloat . FH.floatFromBits e p . BV.asUnsigned <$> W4.groundEval evalFn f
    VarFinSeq n vs ->
      VarFinSeq n <$> mapM (varShapeToConcrete evalFn) vs
    VarTuple vs ->
      VarTuple <$> mapM (varShapeToConcrete evalFn) vs
    VarRecord fs ->
      VarRecord <$> traverse (varShapeToConcrete evalFn) fs

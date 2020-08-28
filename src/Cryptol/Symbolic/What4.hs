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

import Control.Concurrent.Async
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

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Concrete.FloatHelpers as Concrete
import qualified Cryptol.Eval.Backend as Eval
import qualified Cryptol.Eval.Value as Eval
import qualified Cryptol.Eval.Type as Eval
import           Cryptol.Eval.What4
import qualified Cryptol.Eval.What4.SFloat as W4
import           Cryptol.Symbolic
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import           Cryptol.Utils.Ident (Ident)
import           Cryptol.Utils.Logger(logPutStrLn)
import           Cryptol.Utils.Panic (panic)
import           Cryptol.Utils.RecordMap

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


doEval :: MonadIO m => Eval.Eval a -> m a
doEval m = liftIO $ Eval.runEval m

-- | Returns definitions, together with the value and it safety predicate.
doW4Eval ::
  (W4.IsExprBuilder sym, MonadIO m) =>
  sym -> W4Eval sym a -> m (W4Defs sym (W4.Pred sym, a))
doW4Eval sym m =
  do res <- liftIO $ Eval.runEval (w4Eval m sym)
     case w4Result res of
       W4Error err  -> liftIO (X.throwIO err)
       W4Result p x -> pure res { w4Result = (p,x) }


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



-- TODO? move this?
allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedNonParamModules

setupAdapterOptions :: W4ProverConfig -> W4.ExprBuilder t CryptolState fs -> IO ()
setupAdapterOptions cfg sym =
   case cfg of
     W4ProverConfig p -> setupAnAdapter p
     W4Portfolio ps -> mapM_ setupAnAdapter ps

  where
  setupAnAdapter (AnAdapter adpt) =
    W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)


-- | Simulate and manipulate query into a form suitable to be sent
-- to a solver.
prepareQuery ::
  W4.IsSymExprBuilder sym =>
  sym ->
  ProverCommand ->
  M.ModuleT IO (Either String
                       ([FinType],[VarShape sym],W4.Pred sym, W4.Pred sym)
               )
prepareQuery sym ProverCommand { .. } =
  case predArgTypes pcQueryType pcSchema of
    Left msg -> pure (Left msg)
    Right ts ->
      do args <- liftIO (mapM (freshVariable sym) ts)
         res  <- simulate args
         liftIO
           do -- add the collected definitions to the goal
              let (safety,prop') = w4Result res
              b <- W4.andPred sym (w4Defs res) prop'

              -- Ignore the safety condition if the flag is set
              let safety' = if pcIgnoreSafety then W4.truePred sym else safety

              Right <$>
                case pcQueryType of
                  ProveQuery ->
                    do q <- W4.notPred sym =<< W4.andPred sym safety' b
                       pure (ts,args,safety',q)

                  SafetyQuery ->
                    do q <- W4.notPred sym safety
                       pure (ts,args,safety,q)

                  SatQuery _ ->
                    do q <- W4.andPred sym safety' b
                       pure (ts,args,safety',q)
  where
  simulate args =
    do let lPutStrLn = M.withLogger logPutStrLn
       when pcVerbose (lPutStrLn "Simulating...")
       modEnv <- M.getModuleEnv
       doW4Eval sym
         do let tbl = primTable sym
            let ?evalPrim = \i -> Map.lookup i tbl
            let extDgs = allDeclGroups modEnv ++ pcExtraDecls
            env <- Eval.evalDecls (What4 sym) extDgs mempty
            v   <- Eval.evalExpr  (What4 sym) env    pcExpr
            appliedVal <-
              foldM Eval.fromVFun v (map (pure . varToSymValue sym) args)

            case pcQueryType of
              SafetyQuery ->
                do _ <- Eval.forceValue (What4 sym) appliedVal
                   pure (W4.truePred sym)

              _ -> pure (Eval.fromVBit appliedVal)





satProve ::
  W4ProverConfig ->
  Bool ->
  ProverCommand ->
  M.ModuleCmd (Maybe String, ProverResult)

satProve solverCfg hashConsing ProverCommand {..} =
  protectStack proverError \(evo, byteReader, modEnv) ->
  M.runModuleM (evo, byteReader, modEnv)
  do sym     <- liftIO makeSym
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
    do sym <- W4.newExprBuilder W4.FloatIEEERepr
                                CryptolState
                                globalNonceGenerator
       setupAdapterOptions solverCfg sym
       when hashConsing (W4.startCaching sym)
       pure sym

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
   do sym <- liftIO makeSym
      ok  <- prepareQuery sym ProverCommand { .. }
      liftIO
        case ok of
          Left msg -> return (Just msg)
          Right (_ts,_args,_safety,query) ->
            do outputContinuation
                  (\hdl -> solver_adapter_write_smt2 adpt sym hdl [query])
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
  sym ->
  W4ProverConfig ->
  PrimMap ->
  W4.LogData ->
  [FinType] ->
  [VarShape sym] ->
  W4.Pred sym ->
  SatNum ->
  IO (Maybe String, ProverResult)
multiSATQuery sym solverCfg primMap logData ts args query (SomeSat n) | n <= 1 =
  singleQuery sym solverCfg primMap logData ts args Nothing query

multiSATQuery _sym (W4Portfolio _) _primMap _logData _ts _args _query _satNum =
  fail "What4 portfolio solver cannot be used for multi SAT queries"

multiSATQuery sym (W4ProverConfig (AnAdapter adpt)) primMap logData ts args query satNum0 =
  do pres <- W4.solver_adapter_check_sat adpt sym logData [query] $ \res ->
         case res of
           W4.Unknown -> return (Left (ProverError "Solver returned UNKNOWN"))
           W4.Unsat _ -> return (Left (ThmResult (map unFinType ts)))
           W4.Sat (evalFn,_) ->
             do model <- computeModel primMap evalFn ts args
                blockingPred <- computeBlockingPred sym evalFn args
                return (Right (model, blockingPred))

     case pres of
       Left res -> pure (Just (solver_adapter_name adpt), res)
       Right (mdl,block) ->
         do mdls <- (mdl:) <$> computeMoreModels [block,query] (decSatNum satNum0)
            return (Just (solver_adapter_name adpt), AllSatResult mdls)

  where

  computeMoreModels _qs (SomeSat n) | n <= 0 = return [] -- should never happen...
  computeMoreModels qs (SomeSat n) | n <= 1 = -- final model
    W4.solver_adapter_check_sat adpt sym logData qs $ \res ->
         case res of
           W4.Unknown -> return []
           W4.Unsat _ -> return []
           W4.Sat (evalFn,_) ->
             do model <- computeModel primMap evalFn ts args
                return [model]

  computeMoreModels qs satNum =
    do pres <- W4.solver_adapter_check_sat adpt sym logData qs $ \res ->
         case res of
           W4.Unknown -> return Nothing
           W4.Unsat _ -> return Nothing
           W4.Sat (evalFn,_) ->
             do model <- computeModel primMap evalFn ts args
                blockingPred <- computeBlockingPred sym evalFn args
                return (Just (model, blockingPred))

       case pres of
         Nothing -> return []
         Just (mdl, block) ->
           (mdl:) <$> computeMoreModels (block:qs) (decSatNum satNum)

singleQuery ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  sym ->
  W4ProverConfig ->
  PrimMap ->
  W4.LogData ->
  [FinType] ->
  [VarShape sym] ->
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
  do pres <- W4.solver_adapter_check_sat adpt sym logData [query] $ \res ->
         case res of
           W4.Unknown -> return (ProverError "Solver returned UNKNOWN")
           W4.Unsat _ -> return (ThmResult (map unFinType ts))
           W4.Sat (evalFn,_) ->
             do model <- computeModel primMap evalFn ts args
                case msafe of
                  Just s ->
                    do s' <- W4.groundEval evalFn s
                       let cexType = if s' then PredicateFalsified else SafetyViolation
                       return (CounterExample cexType model)
                  Nothing -> return (AllSatResult [ model ])

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
    VarRational n d ->
      do n' <- W4.intLit sym =<< W4.groundEval evalFn n
         d' <- W4.intLit sym =<< W4.groundEval evalFn d
         x <- W4.intMul sym n d'
         y <- W4.intMul sym n' d
         W4.notPred sym =<< W4.intEq sym x y
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

    VarFinSeq _n _ vs -> computeBlockingPred sym evalFn vs
    VarTuple vs     -> computeBlockingPred sym evalFn vs
    VarRecord fs    -> computeBlockingPred sym evalFn (recordElements fs)

computeModel ::
  PrimMap ->
  W4.GroundEvalFn t ->
  [FinType] ->
  [VarShape (W4.ExprBuilder t CryptolState fm)] ->
  IO [(Type, Expr, Concrete.Value)]
computeModel _ _ [] [] = return []
computeModel primMap evalFn (t:ts) (v:vs) =
  do v' <- varToConcreteValue evalFn v
     let t' = unFinType t
     e <- doEval (Concrete.toExpr primMap t' v') >>= \case
             Nothing -> panic "computeModel" ["could not compute counterexample expression"]
             Just e  -> pure e
     zs <- computeModel primMap evalFn ts vs
     return ((t',e,v'):zs)
computeModel _ _ _ _ = panic "computeModel" ["type/value list mismatch"]


data VarShape sym
  = VarBit (W4.Pred sym)
  | VarInteger (W4.SymInteger sym)
  | VarRational (W4.SymInteger sym) (W4.SymInteger sym)
  | VarFloat (W4.SFloat sym)
  | VarWord (SW.SWord sym)
  | VarFinSeq Int Eval.TValue [VarShape sym]
  | VarTuple [VarShape sym]
  | VarRecord (RecordMap Ident (VarShape sym))

freshVariable :: W4.IsSymExprBuilder sym => sym -> FinType -> IO (VarShape sym)
freshVariable sym ty =
  case ty of
    FTBit         -> VarBit      <$> W4.freshConstant sym W4.emptySymbol W4.BaseBoolRepr
    FTInteger     -> VarInteger  <$> W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
    FTRational    -> VarRational
                        <$> W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
                        <*> W4.freshBoundedInt sym W4.emptySymbol (Just 1) Nothing
    FTIntMod 0    -> panic "freshVariable" ["0 modulus not allowed"]
    FTIntMod n    -> VarInteger  <$> W4.freshBoundedInt sym W4.emptySymbol (Just 0) (Just (n-1))
    FTFloat e p   -> VarFloat    <$> W4.fpFresh sym e p
    FTSeq n FTBit -> VarWord     <$> SW.freshBV sym W4.emptySymbol (toInteger n)
    FTSeq n t     -> VarFinSeq n (finTypeValue t) <$>
                        sequence (replicate n (freshVariable sym t))
    FTTuple ts    -> VarTuple    <$> mapM (freshVariable sym) ts
    FTRecord fs   -> VarRecord   <$> traverse (freshVariable sym) fs

varToSymValue :: W4.IsExprBuilder sym => sym -> VarShape sym -> Value sym
varToSymValue sym var =
  case var of
    VarBit b     -> Eval.VBit b
    VarInteger i -> Eval.VInteger i
    VarRational n d -> Eval.VRational (Eval.SRational n d)
    VarWord w    -> Eval.VSeq (Nat (SW.bvWidth w)) Eval.TVBit (Eval.unpackSeqMap' w)
    VarFloat f   -> Eval.VFloat f
    VarFinSeq n a vs -> Eval.VSeq (Nat (toInteger n)) a
                         (Eval.finiteSeqMap' (map (pure . varToSymValue sym) vs))
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
    VarRational n d ->
       Eval.VRational <$> (Eval.SRational <$> W4.groundEval evalFn n <*> W4.groundEval evalFn d)
    VarWord SW.ZBV     -> pure $ Eval.VSeq (Nat 0) Eval.TVBit (Eval.voidSeqMap)
    VarWord (SW.DBV x) ->
       do let w = W4.intValue (W4.bvWidth x)
          bv <- Concrete.mkBv w . BV.asUnsigned <$> W4.groundEval evalFn x
          pure $ Eval.VSeq (Nat w) Eval.TVBit (Eval.unpackSeqMap' bv)
    VarFloat fv@(W4.SFloat f) ->
      do let (e,p) = W4.fpSize fv
         bits <- W4.groundEval evalFn f
         pure $ Eval.VFloat $ Concrete.floatFromBits e p $ BV.asUnsigned bits

    VarFinSeq n a vs ->
       do vs' <- mapM (varToConcreteValue evalFn) vs
          pure (Eval.VSeq (Nat (toInteger n)) a (Eval.finiteSeqMap' (map pure vs')))
    VarTuple vs ->
       do vs' <- mapM (varToConcreteValue evalFn) vs
          pure (Eval.VTuple (map pure vs'))
    VarRecord fs ->
       do fs' <- traverse (varToConcreteValue evalFn) fs
          pure (Eval.VRecord (fmap pure fs'))


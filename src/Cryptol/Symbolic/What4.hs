-- |
-- Module      :  Cryptol.Symbolic.What4
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
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
import Control.Monad (when, foldM, forM_, void)
import qualified Control.Exception as X
import System.IO (Handle, IOMode(..), withFile)
import Data.Time
import Data.IORef
import Data.List (intercalate, tails, inits)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Proxy
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NE
import System.Exit

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M
import qualified Cryptol.ModuleSystem.Name as M

import qualified Cryptol.Backend.FloatHelpers as FH
import           Cryptol.Backend.What4

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.Type (TValue)
import           Cryptol.Eval.What4

import           Cryptol.Parser.Position (emptyRange)
import           Cryptol.Symbolic
import           Cryptol.TypeCheck.AST
import           Cryptol.Utils.Logger(logPutStrLn,logPutStr,Logger)
import           Cryptol.Utils.Ident (preludeReferenceName, prelPrim, identText)

import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.GroundEval as W4
import qualified What4.SatResult as W4
import qualified What4.SFloat as W4
import qualified What4.SWord as SW
import           What4.Solver
import qualified What4.Solver.Boolector as W4
import qualified What4.Solver.CVC4 as W4
import qualified What4.Solver.CVC5 as W4
import qualified What4.Solver.ExternalABC as W4
import qualified What4.Solver.Yices as W4
import qualified What4.Solver.Z3 as W4
import qualified What4.Solver.Adapter as W4
import qualified What4.Protocol.Online as W4
import qualified What4.Protocol.SMTLib2 as W4
import qualified What4.ProblemFeatures as W4

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
  do res <- liftIO $ Eval.runEval mempty (w4Eval m sym)
     case res of
       W4Error err  -> liftIO (X.throwIO err)
       W4Result p x -> pure (p,x)


data AnAdapter
  = AnAdapter (forall st. SolverAdapter st)
  | forall s. W4.OnlineSolver s =>
     AnOnlineAdapter
       String
       W4.ProblemFeatures
       [W4.ConfigDesc]
       (Proxy s)

data W4ProverConfig
  = W4ProverConfig AnAdapter
  | W4OfflineConfig
  | W4Portfolio (NonEmpty AnAdapter)

proverConfigs :: [(String, W4ProverConfig)]
proverConfigs =
  [ ("w4-cvc4"      , W4ProverConfig cvc4OnlineAdapter)
  , ("w4-cvc5"      , W4ProverConfig cvc5OnlineAdapter)
  , ("w4-yices"     , W4ProverConfig yicesOnlineAdapter)
  , ("w4-z3"        , W4ProverConfig z3OnlineAdapter)
  , ("w4-boolector" , W4ProverConfig boolectorOnlineAdapter)

  , ("w4-abc"       , W4ProverConfig (AnAdapter W4.externalABCAdapter))

  , ("w4-offline"   , W4OfflineConfig )
  , ("w4-any"       , allSolvers)
  ]

z3OnlineAdapter :: AnAdapter
z3OnlineAdapter =
  AnOnlineAdapter "Z3" W4.z3Features W4.z3Options
         (Proxy :: Proxy (W4.Writer W4.Z3))

yicesOnlineAdapter :: AnAdapter
yicesOnlineAdapter =
  AnOnlineAdapter "Yices" W4.yicesDefaultFeatures W4.yicesOptions
         (Proxy :: Proxy W4.Connection)

cvc4OnlineAdapter :: AnAdapter
cvc4OnlineAdapter =
  AnOnlineAdapter "CVC4" W4.cvc4Features W4.cvc4Options
         (Proxy :: Proxy (W4.Writer W4.CVC4))

cvc5OnlineAdapter :: AnAdapter
cvc5OnlineAdapter =
  AnOnlineAdapter "CVC5" W4.cvc5Features W4.cvc5Options
         (Proxy :: Proxy (W4.Writer W4.CVC5))

boolectorOnlineAdapter :: AnAdapter
boolectorOnlineAdapter =
  AnOnlineAdapter "Boolector" W4.boolectorFeatures W4.boolectorOptions
         (Proxy :: Proxy (W4.Writer W4.Boolector))

allSolvers :: W4ProverConfig
allSolvers = W4Portfolio
  $ z3OnlineAdapter :|
  [ cvc4OnlineAdapter
  , cvc5OnlineAdapter
  , boolectorOnlineAdapter
  , yicesOnlineAdapter
  , AnAdapter W4.externalABCAdapter
  ]

defaultProver :: W4ProverConfig
defaultProver = W4ProverConfig z3OnlineAdapter

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

    Just W4OfflineConfig -> pure (Right ([], W4OfflineConfig))

    Nothing -> pure (Left ("unknown solver name: " ++ nm))

  where
  adapterNames [] = []
  adapterNames (AnAdapter adpt : ps) =
    solver_adapter_name adpt : adapterNames ps
  adapterNames (AnOnlineAdapter n _ _ _ : ps) =
    n : adapterNames ps

  filterAdapters [] = pure []
  filterAdapters (p:ps) =
    tryAdapter p >>= \case
      Just _err -> filterAdapters ps
      Nothing   -> (p:) <$> filterAdapters ps

  tryAdapter :: AnAdapter -> IO (Maybe X.SomeException)

  tryAdapter (AnAdapter adpt) =
     do sym <- W4.newExprBuilder W4.FloatIEEERepr CryptolState globalNonceGenerator
        W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)
        W4.smokeTest sym adpt

  tryAdapter (AnOnlineAdapter _ fs opts (_ :: Proxy s)) = test `X.catch` (pure . Just)
   where
    test =
      do sym <- W4.newExprBuilder W4.FloatIEEERepr CryptolState globalNonceGenerator
         W4.extendConfig opts (W4.getConfiguration sym)
         (proc :: W4.SolverProcess GlobalNonceGenerator s) <- W4.startSolverProcess fs Nothing sym
         res <- W4.checkSatisfiable proc "smoke test" (W4.falsePred sym)
         case res of
           W4.Unsat () -> return ()
           _ -> fail "smoke test failed, expected UNSAT!"
         void (W4.shutdownSolverProcess proc)
         return Nothing

proverError :: String -> M.ModuleCmd (Maybe String, ProverResult)
proverError msg minp =
  return (Right ((Nothing, ProverError msg), M.minpModuleEnv minp), [])


data CryptolState t = CryptolState


setupAdapterOptions :: W4ProverConfig -> W4.ExprBuilder t CryptolState fs -> IO ()
setupAdapterOptions cfg sym =
   case cfg of
     W4ProverConfig p -> setupAnAdapter p
     W4Portfolio ps -> mapM_ setupAnAdapter ps
     W4OfflineConfig -> return ()

  where
  setupAnAdapter (AnAdapter adpt) =
    W4.extendConfig (W4.solver_adapter_config_options adpt) (W4.getConfiguration sym)
  setupAnAdapter (AnOnlineAdapter _n _fs opts _p) =
    W4.extendConfig opts (W4.getConfiguration sym)

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
prepareQuery sym ProverCommand { .. } = do
  ntEnv <- M.getNewtypes
  case predArgTypes pcQueryType pcSchema of
    Left msg -> pure (Left msg)
    Right ts ->
      do args <- liftIO (mapM (freshVar (what4FreshFns (w4 sym))) ts)
         (safety,b) <- simulate ntEnv args
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
  simulate ntEnv args =
    do let lPutStrLn = M.withLogger logPutStrLn
       when pcVerbose (lPutStrLn "Simulating...")

       ds <- do (_mp, ent) <- M.loadModuleFrom True (M.FromModule preludeReferenceName)
                let m = tcTopEntityToModule ent
                let decls = mDecls m
                let nms = fst <$> Map.toList (M.ifDecls (M.ifDefines (M.genIface m)))
                let ds = Map.fromList [ (prelPrim (identText (M.nameIdent nm)), EWhere (EVar nm) decls) | nm <- nms ]
                pure ds

       getEOpts <- M.getEvalOptsAction
       let tbl = primTable sym getEOpts
       let ?evalPrim = \i -> (Right <$> Map.lookup i tbl) <|>
                             (Left <$> Map.lookup i ds)
       let ?range = emptyRange
       callStacks <- M.getCallStacks
       let ?callStacks = callStacks

       modEnv <- M.getModuleEnv
       let extDgs = M.allDeclGroups modEnv ++ pcExtraDecls

       doW4Eval (w4 sym)
         do env <- Eval.evalDecls sym extDgs =<<
                     Eval.evalNewtypeDecls sym ntEnv mempty

            v   <- Eval.evalExpr  sym env    pcExpr
            appliedVal <-
              foldM (Eval.fromVFun sym) v (map (pure . varShapeToValue sym) args)

            case pcQueryType of
              SafetyQuery ->
                do Eval.forceValue appliedVal
                   pure (W4.truePred (w4 sym))

              _ -> pure (Eval.fromVBit appliedVal)


satProve ::
  W4ProverConfig ->
  Bool {- ^ hash consing -} ->
  Bool {- ^ warn on uninterpreted functions -} ->
  ProverCommand ->
  M.ModuleCmd (Maybe String, ProverResult)

satProve solverCfg hashConsing warnUninterp pc@ProverCommand {..} =
  protectStack proverError \modIn ->
  M.runModuleM modIn
  do w4sym   <- liftIO makeSym
     defVar  <- liftIO (newMVar (W4.truePred w4sym))
     funVar  <- liftIO (newMVar mempty)
     uninterpWarnVar <- liftIO (newMVar mempty)
     let sym = What4 w4sym defVar funVar uninterpWarnVar
     logData <- M.withLogger doLog ()
     start   <- liftIO getCurrentTime
     query   <- prepareQuery sym ProverCommand { .. }
     primMap <- M.getPrimMap
     when warnUninterp
       (M.withLogger printUninterpWarn =<< liftIO (readMVar uninterpWarnVar))
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
            singleQuery sym solverCfg pc primMap logData ts args (Just safety) query

          SafetyQuery ->
            singleQuery sym solverCfg pc primMap logData ts args (Just safety) query

          SatQuery num ->
            multiSATQuery sym solverCfg pc primMap logData ts args query num

printUninterpWarn :: Logger -> Set Text -> IO ()
printUninterpWarn lg uninterpWarns =
  case Set.toList uninterpWarns of
    []  -> pure ()
    [x] -> logPutStrLn lg ("[Warning] Uninterpreted functions used to represent " ++ Text.unpack x ++ " operations.")
    xs  -> logPutStr lg $ unlines
             [ "[Warning] Uninterpreted functions used to represent the following operations:"
             , "  " ++ intercalate ", " (map Text.unpack xs) ]

satProveOffline ::
  Bool {- ^ hash consing -} ->
  Bool {- ^ warn on uninterpreted functions -} ->
  ProverCommand ->
  ((Handle -> IO ()) -> IO ()) ->
  M.ModuleCmd (Maybe String)

satProveOffline hashConsing warnUninterp ProverCommand{ .. } outputContinuation =

  protectStack onError \modIn ->
  M.runModuleM modIn
   do w4sym <- liftIO makeSym
      defVar  <- liftIO (newMVar (W4.truePred w4sym))
      funVar  <- liftIO (newMVar mempty)
      uninterpWarnVar <- liftIO (newMVar mempty)
      let sym = What4 w4sym defVar funVar uninterpWarnVar
      ok  <- prepareQuery sym ProverCommand { .. }
      when warnUninterp
        (M.withLogger printUninterpWarn =<< liftIO (readMVar uninterpWarnVar))
      liftIO
        case ok of
          Left msg -> return (Just msg)
          Right (_ts,_args,_safety,query) ->
            do outputContinuation (\hdl -> W4.writeZ3SMT2File w4sym hdl [query])
               return Nothing
  where
  makeSym =
    do sym <- W4.newExprBuilder W4.FloatIEEERepr CryptolState globalNonceGenerator
       W4.extendConfig W4.z3Options (W4.getConfiguration sym)
       when hashConsing  (W4.startCaching sym)
       pure sym

  onError msg minp = pure (Right (Just msg, M.minpModuleEnv minp), [])


{-
decSatNum :: SatNum -> SatNum
decSatNum (SomeSat n) | n > 0 = SomeSat (n-1)
decSatNum n = n
-}


multiSATQuery :: forall sym t fm.
  sym ~ W4.ExprBuilder t CryptolState fm =>
  What4 sym ->
  W4ProverConfig ->
  ProverCommand ->
  PrimMap ->
  W4.LogData ->
  [FinType] ->
  [VarShape (What4 sym)] ->
  W4.Pred sym ->
  SatNum ->
  IO (Maybe String, ProverResult)

multiSATQuery sym solverCfg pc primMap logData ts args query (SomeSat n) | n <= 1 =
  singleQuery sym solverCfg pc primMap logData ts args Nothing query

multiSATQuery _sym W4OfflineConfig _pc _primMap _logData _ts _args _query _satNum =
  fail "What4 offline solver cannot be used for multi-SAT queries"

multiSATQuery _sym (W4Portfolio _) _pc _primMap _logData _ts _args _query _satNum =
  fail "What4 portfolio solver cannot be used for multi-SAT queries"

multiSATQuery _sym (W4ProverConfig (AnAdapter adpt)) _pc _primMap _logData _ts _args _query _satNum =
  fail ("Solver " ++ solver_adapter_name adpt ++ " does not support incremental solving and " ++
        "cannot be used for multi-SAT queries.")

multiSATQuery sym (W4ProverConfig (AnOnlineAdapter nm fs _opts (_ :: Proxy s)))
               ProverCommand{..} primMap _logData ts args query satNum0 =
    withMaybeFile pcSmtFile WriteMode $ \smtFileHdl ->
    X.bracket
      (W4.startSolverProcess fs smtFileHdl (w4 sym))
      (void . W4.shutdownSolverProcess)
      (\ (proc :: W4.SolverProcess t s) ->
        do W4.assume (W4.solverConn proc) query
           res <- W4.checkAndGetModel proc "query"
           case res of
             W4.Unknown -> return (Just nm, ProverError "Solver returned UNKNOWN")
             W4.Unsat _ -> return (Just nm, ThmResult (map unFinType ts))
             W4.Sat evalFn ->
               do xs <- mapM (varShapeToConcrete evalFn) args
                  let mdl = computeModel primMap ts xs
                  -- NB, we flatten these shapes to make sure that we can split
                  -- our search across all of the atomic variables
                  let vs = flattenShapes args []
                  let cs = flattenShapes xs []
                  mdls <- runMultiSat satNum0 $
                            do yield mdl
                               computeMoreModels proc vs cs
                  return (Just nm, AllSatResult mdls))

  where
  -- This search procedure uses incremental solving and push/pop to split on the concrete
  -- values of variables, while also helping to prevent the accumulation of unhelpful
  -- lemmas in the solver state.  This algorithm is basically taken from:
  --   http://theory.stanford.edu/%7Enikolaj/programmingz3.html#sec-blocking-evaluations
  computeMoreModels ::
    W4.SolverProcess t s ->
    [VarShape (What4 sym)] ->
    [VarShape Concrete.Concrete] ->
    MultiSat ()
  computeMoreModels proc vs cs =
    -- Enumerate all the ways to split up the current model
    forM_ (computeSplits vs cs) $ \ (prefix, vi, ci, suffix) ->
      do -- open a new solver frame
         liftIO $ W4.push proc
         -- force the selected pair to be different
         liftIO $ W4.assume (W4.solverConn proc) =<< W4.notPred (w4 sym) =<< computeModelPred sym vi ci
         -- force the prefix values to be the same
         liftIO $ forM_ prefix $ \(v,c) ->
           W4.assume (W4.solverConn proc) =<< computeModelPred sym v c
         -- under these assumptions, find all the remaining models
         findMoreModels proc (vi:suffix)
         -- pop the current assumption frame
         liftIO $ W4.pop proc

  findMoreModels ::
    W4.SolverProcess t s ->
    [VarShape (What4 sym)] ->
    MultiSat ()
  findMoreModels proc vs =
    -- see if our current assumptions are consistent
    do res <- liftIO (W4.checkAndGetModel proc "find model")
       case res of
         -- if the solver gets stuck, drop all the way out and stop search
         W4.Unknown -> done
         -- if our assumptions are already unsatisfiable, stop search and return
         W4.Unsat _ -> return ()
         W4.Sat evalFn ->
           -- We found a model.  Record it and then use it to split the remaining
           -- search variables some more.
           do xs <- liftIO (mapM (varShapeToConcrete evalFn) args)
              yield (computeModel primMap ts xs)
              cs <- liftIO (mapM (varShapeToConcrete evalFn) vs)
              computeMoreModels proc vs cs

-- == Support operations for multi-SAT ==
type Models = [[(TValue, Expr, Concrete.Value)]]

newtype MultiSat a =
  MultiSat { unMultiSat ::  Models -> SatNum -> (a -> Models -> SatNum -> IO Models) -> IO Models }

instance Functor MultiSat where
  fmap f m = MultiSat (\ms satNum k -> unMultiSat m ms satNum (k . f))

instance Applicative MultiSat where
  pure x = MultiSat (\ms satNum k -> k x ms satNum)
  mf <*> mx = mf >>= \f -> fmap f mx

instance Monad MultiSat where
  m >>= f = MultiSat (\ms satNum k -> unMultiSat m ms satNum (\x ms' satNum' -> unMultiSat (f x) ms' satNum' k))

instance MonadIO MultiSat where
  liftIO m = MultiSat (\ms satNum k -> do x <- m; k x ms satNum)

runMultiSat :: SatNum -> MultiSat a -> IO Models
runMultiSat satNum m = reverse <$> unMultiSat m [] satNum (\_ ms _ -> return ms)

done :: MultiSat a
done = MultiSat (\ms _satNum _k -> return ms)

yield :: [(TValue, Expr, Concrete.Value)] -> MultiSat ()
yield mdl = MultiSat (\ms satNum k ->
  case satNum of
    SomeSat n
      | n > 1 -> k () (mdl:ms) (SomeSat (n-1))
      | otherwise -> return (mdl:ms)
    _ -> k () (mdl:ms) satNum)

-- Compute all the ways to split a sequences of variables
-- and concrete values for those variables.  Each element
-- of the list consists of a prefix of (varaible,value)
-- pairs whose values we will fix, a single (varaible,value)
-- pair that we will force to be different, and a list of
-- additional unconstrained variables.
computeSplits ::
  [VarShape (What4 sym)] ->
  [VarShape Concrete.Concrete] ->
  [ ( [(VarShape (What4 sym), VarShape Concrete.Concrete)]
    , VarShape (What4 sym)
    , VarShape Concrete.Concrete
    , [VarShape (What4 sym)]
    )
  ]
computeSplits vs cs = reverse
  [ (prefix, v, c, tl)
  | prefix <- inits (zip vs cs)
  | v      <- vs
  | c      <- cs
  | tl     <- tail (tails vs)
  ]
-- == END Support operations for multi-SAT ==

singleQuery ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  What4 sym ->
  W4ProverConfig ->
  ProverCommand ->
  PrimMap ->
  W4.LogData ->
  [FinType] ->
  [VarShape (What4 sym)] ->
  Maybe (W4.Pred sym) {- ^ optional safety predicate.  Nothing = SAT query -} ->
  W4.Pred sym ->
  IO (Maybe String, ProverResult)

singleQuery _ W4OfflineConfig _pc _primMap _logData _ts _args _msafe _query =
  -- this shouldn't happen...
  fail "What4 offline solver cannot be used for direct queries"

singleQuery sym (W4Portfolio ps) pc primMap logData ts args msafe query =
  do as <- mapM async [ singleQuery sym (W4ProverConfig p) pc primMap logData ts args msafe query
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

singleQuery sym (W4ProverConfig (AnAdapter adpt)) _pc primMap logData ts args msafe query =
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

singleQuery sym (W4ProverConfig (AnOnlineAdapter nm fs _opts (_ :: Proxy s)))
              ProverCommand{..} primMap _logData ts args msafe query =
  withMaybeFile pcSmtFile WriteMode $ \smtFileHdl ->
  X.bracket
    (W4.startSolverProcess fs smtFileHdl (w4 sym))
    (void . W4.shutdownSolverProcess)
    (\ (proc :: W4.SolverProcess t s) ->
        do W4.assume (W4.solverConn proc) query
           res <- W4.checkAndGetModel proc "query"
           case res of
             W4.Unknown -> return (Just nm, ProverError "Solver returned UNKNOWN")
             W4.Unsat _ -> return (Just nm, ThmResult (map unFinType ts))
             W4.Sat evalFn ->
               do xs <- mapM (varShapeToConcrete evalFn) args
                  let model = computeModel primMap ts xs
                  case msafe of
                    Just s ->
                      do s' <- W4.groundEval evalFn s
                         let cexType = if s' then PredicateFalsified else SafetyViolation
                         return (Just nm, CounterExample cexType model)
                    Nothing -> return (Just nm, AllSatResult [ model ])
    )


-- | Like 'withFile', but lifted to work over 'Maybe'.
withMaybeFile :: Maybe FilePath -> IOMode -> (Maybe Handle -> IO r) -> IO r
withMaybeFile mbFP mode action =
  case mbFP of
    Just fp -> withFile fp mode (action . Just)
    Nothing -> action Nothing

computeModelPred ::
  sym ~ W4.ExprBuilder t CryptolState fm =>
  What4 sym ->
  VarShape (What4 sym) ->
  VarShape Concrete.Concrete ->
  IO (W4.Pred sym)
computeModelPred sym v c =
  snd <$> doW4Eval (w4 sym) (varModelPred sym (v, c))

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
      let (e,p) = W4.fpSize fv
       in VarFloat . FH.BF e p <$> W4.groundEval evalFn f
    VarFinSeq n vs ->
      VarFinSeq n <$> mapM (varShapeToConcrete evalFn) vs
    VarTuple vs ->
      VarTuple <$> mapM (varShapeToConcrete evalFn) vs
    VarRecord fs ->
      VarRecord <$> traverse (varShapeToConcrete evalFn) fs

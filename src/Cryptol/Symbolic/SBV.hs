-- |
-- Module      :  Cryptol.Symbolic.SBV
-- Copyright   :  (c) 2013-2016 Galois, Inc.
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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic.SBV
 ( proverNames
 , checkProverInstallation
 , satProve
 , satProveOffline
 ) where


import Control.Monad.IO.Class
import Control.Monad (replicateM, when, zipWithM, foldM)
import Control.Monad.Writer (WriterT, runWriterT, tell, lift)
import Data.List (intercalate, genericLength)
import qualified Data.Map as Map
import qualified Control.Exception as X

import qualified Data.SBV.Dynamic as SBV
import           Data.SBV (Timing(SaveTiming))
import           Data.SBV.Internals (showTDiff)
import           Data.Time (NominalDiffTime)

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.Eval.Concrete (Concrete(..))
import qualified Cryptol.Eval.Monad as Eval

import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.SBV
import Cryptol.Symbolic
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Logger(logPutStrLn)

import Prelude ()
import Prelude.Compat

doEval :: MonadIO m => Eval.EvalOpts -> Eval.Eval a -> m a
doEval evo m = liftIO $ Eval.runEval evo m

doSBVEval :: MonadIO m => Eval.EvalOpts -> SBVEval a -> m (SBV.SVal, a)
doSBVEval evo m =
  (liftIO $ Eval.runEval evo (sbvEval m)) >>= \case
    SBVError err -> liftIO (X.throwIO err)
    SBVResult p x -> pure (p, x)

-- External interface ----------------------------------------------------------

proverConfigs :: [(String, SBV.SMTConfig)]
proverConfigs =
  [ ("cvc4"     , SBV.cvc4     )
  , ("yices"    , SBV.yices    )
  , ("z3"       , SBV.z3       )
  , ("boolector", SBV.boolector)
  , ("mathsat"  , SBV.mathSAT  )
  , ("abc"      , SBV.abc      )
  , ("offline"  , SBV.defaultSMTCfg )
  , ("any"      , SBV.defaultSMTCfg )

  , ("sbv-cvc4"     , SBV.cvc4     )
  , ("sbv-yices"    , SBV.yices    )
  , ("sbv-z3"       , SBV.z3       )
  , ("sbv-boolector", SBV.boolector)
  , ("sbv-mathsat"  , SBV.mathSAT  )
  , ("sbv-abc"      , SBV.abc      )
  , ("sbv-offline"  , SBV.defaultSMTCfg )
  , ("sbv-any"      , SBV.defaultSMTCfg )
  ]

-- | The names of all the solvers supported by SBV
proverNames :: [String]
proverNames = map fst proverConfigs

lookupProver :: String -> SBV.SMTConfig
lookupProver s =
  case lookup s proverConfigs of
    Just cfg -> cfg
    -- should be caught by UI for setting prover user variable
    Nothing  -> panic "Cryptol.Symbolic.SBV" [ "invalid prover: " ++ s ]

satSMTResults :: SBV.SatResult -> [SBV.SMTResult]
satSMTResults (SBV.SatResult r) = [r]

allSatSMTResults :: SBV.AllSatResult -> [SBV.SMTResult]
allSatSMTResults (SBV.AllSatResult (_, _, _, rs)) = rs

-- | Check if the named solver can be found and invoked
--   in the current solver environment.
checkProverInstallation :: String -> IO Bool
checkProverInstallation s =
  do let prover = lookupProver s
     SBV.sbvCheckSolverInstallation prover

thmSMTResults :: SBV.ThmResult -> [SBV.SMTResult]
thmSMTResults (SBV.ThmResult r) = [r]

proverError :: String -> M.ModuleCmd (Maybe String, ProverResult)
proverError msg (_,modEnv) =
  return (Right ((Nothing, ProverError msg), modEnv), [])


runSingleProver ::
  ProverCommand ->
  [SBV.SMTConfig] ->
  (SBV.SMTConfig -> SBV.Symbolic SBV.SVal -> IO res) ->
  (res -> [SBV.SMTResult]) ->
  SBV.Symbolic SBV.SVal ->
  M.ModuleT IO (Maybe String, [SBV.SMTResult])
runSingleProver ProverCommand{..} provers callSolver processResult e = do
  let lPutStrLn = M.withLogger logPutStrLn

  case provers of
    [prover] -> do
      when pcVerbose $
        lPutStrLn $ "Trying proof with " ++
                                  show (SBV.name (SBV.solver prover))
      res <- M.io (callSolver prover e)
      when pcVerbose $
        lPutStrLn $ "Got result from " ++
                                  show (SBV.name (SBV.solver prover))
      return (Just (show (SBV.name (SBV.solver prover))), processResult res)
    _ ->
      return ( Nothing
             , [ SBV.ProofError
                   prover
                   [":sat with option prover=any requires option satNum=1"]
                   Nothing
               | prover <- provers ]
             )

runMultiProvers ::
  ProverCommand ->
  [SBV.SMTConfig] ->
  ([SBV.SMTConfig] -> SBV.Symbolic SBV.SVal -> IO (SBV.Solver, NominalDiffTime, res)) ->
  (res -> [SBV.SMTResult]) ->
  SBV.Symbolic SBV.SVal ->
  M.ModuleT IO (Maybe String, [SBV.SMTResult])
runMultiProvers ProverCommand{..} provers callSolvers processResult e = do
  let lPutStrLn = M.withLogger logPutStrLn

  when pcVerbose $
    lPutStrLn $ "Trying proof with " ++
            intercalate ", " (map (show . SBV.name . SBV.solver) provers)
  (firstProver, timeElapsed, res) <- M.io (callSolvers provers e)
  when pcVerbose $
    lPutStrLn $ "Got result from " ++ show firstProver ++
                                      ", time: " ++ showTDiff timeElapsed
  return (Just (show firstProver), processResult res)

-- | Select the appropriate solver or solvers from the given prover command,
--   and invoke those solvers on the given symbolic value.
runProver :: ProverCommand -> SBV.Symbolic SBV.SVal -> M.ModuleT IO (Maybe String, [SBV.SMTResult])
runProver pc@ProverCommand{..} x =
  do let mSatNum = case pcQueryType of
                     SatQuery (SomeSat n) -> Just n
                     SatQuery AllSat -> Nothing
                     ProveQuery -> Nothing

     provers <-
       case pcProverName of
         "any" -> M.io SBV.sbvAvailableSolvers
         "sbv-any" -> M.io SBV.sbvAvailableSolvers
         _ -> return [(lookupProver pcProverName)
                        { SBV.transcript = pcSmtFile
                        , SBV.allSatMaxModelCount = mSatNum
                        }]

     let provers' = [ p { SBV.timing = SaveTiming pcProverStats
                        , SBV.verbose = pcVerbose
                        , SBV.validateModel = pcValidate
                        }
                    | p <- provers
                    ]

     case pcQueryType of
        ProveQuery -> runMultiProvers pc provers' SBV.proveWithAny thmSMTResults x
        SatQuery sn -> case sn of
          SomeSat 1 -> runMultiProvers pc provers' SBV.satWithAny satSMTResults x
          _         -> runSingleProver pc provers' SBV.allSatWith allSatSMTResults x


-- | Prepare a symbolic query by symbolically simulating the expression found in
--   the @ProverQuery@.  The result will either be an error or a list of the types
--   of the symbolic inputs and the symbolic value to supply to the solver.
--
--   Note that the difference between sat and prove queries is reflected later
--   in `runProver` where we call different SBV methods depending on the mode,
--   so we do _not_ negate the goal here.  Moreover, assumptions are added
--   using conjunction for sat queries and implication for prove queries.
--
--   For safety properties, we want to add them as an additional goal
--   when we do prove queries, and an additional assumption when we do
--   sat queries.  In both cases, the safety property is combined with
--   the main goal via a conjunction.
prepareQuery ::
  Eval.EvalOpts ->
  M.ModuleEnv ->
  ProverCommand ->
  IO (Either String ([FinType], SBV.Symbolic SBV.SVal))
prepareQuery evo modEnv ProverCommand{..} =
  do let extDgs = M.allDeclGroups modEnv ++ pcExtraDecls

     -- The `tyFn` creates variables that are treated as 'forall'
     -- or 'exists' bound, depending on the sort of query we are doing.
     let tyFn = case pcQueryType of
           SatQuery _ -> existsFinType
           ProveQuery -> forallFinType

     -- The `addAsm` function is used to combine assumptions that
     -- arise from the types of symbolic variables (e.g. Z n values
     -- are assumed to be integers in the range `0 <= x < n`) with
     -- the main content of the query.  We use conjunction or implication
     -- depending on the type of query.
     let addAsm = case pcQueryType of
           ProveQuery -> \x y -> SBV.svOr (SBV.svNot x) y
           SatQuery _ -> \x y -> SBV.svAnd x y

     let ?evalPrim = evalPrim
     case predArgTypes pcSchema of
       Left msg -> return (Left msg)
       Right ts ->
         do when pcVerbose $ logPutStrLn (Eval.evalLogger evo) "Simulating..."
            pure $ Right $ (ts,
              do -- Compute the symbolic inputs, and any domain constraints needed
                 -- according to their types.
                 (args, asms) <- runWriterT (mapM tyFn ts)
                 -- Run the main symbolic computation.  First we populate the
                 -- evaluation environment, then we compute the value, finally
                 -- we apply it to the symbolic inputs.
                 (safety,b) <- doSBVEval evo $
                     do env <- Eval.evalDecls SBV extDgs mempty
                        v <- Eval.evalExpr SBV env pcExpr
                        Eval.fromVBit <$> foldM Eval.fromVFun v (map pure args)
                 return (foldr addAsm (SBV.svAnd safety b) asms))


-- | Turn the SMT results from SBV into a @ProverResult@ that is ready for the Cryptol REPL.
--   There may be more than one result if we made a multi-sat query.
processResults ::
  Eval.EvalOpts ->
  ProverCommand ->
  [FinType] {- ^ Types of the symbolic inputs -} ->
  [SBV.SMTResult] {- ^ Results from the solver -} ->
  M.ModuleT IO ProverResult
processResults evo ProverCommand{..} ts results =
 do let isSat = case pcQueryType of
          ProveQuery -> False
          SatQuery _ -> True

    prims <- M.getPrimMap

    case results of
       -- allSat can return more than one as long as
       -- they're satisfiable
       (SBV.Satisfiable {} : _) -> do
         tevss <- mapM mkTevs results
         return $ AllSatResult tevss
         where
           mkTevs result = do
             let Right (_, cvs) = SBV.getModelAssignment result
                 (vs, _) = parseValues ts cvs
                 sattys = unFinType <$> ts
             satexprs <-
               doEval evo (zipWithM (Concrete.toExpr prims) sattys vs)
             case zip3 sattys <$> (sequence satexprs) <*> pure vs of
               Nothing ->
                 panic "Cryptol.Symbolic.sat"
                   [ "unable to make assignment into expression" ]
               Just tevs -> return $ tevs

       -- prove returns only one
       [SBV.Unsatisfiable {}] ->
         return $ ThmResult (unFinType <$> ts)

       -- unsat returns empty
       [] -> return $ ThmResult (unFinType <$> ts)

       -- otherwise something is wrong
       _ -> return $ ProverError (rshow results)
              where rshow | isSat = show .  SBV.AllSatResult . (False,False,False,)
                          | otherwise = show . SBV.ThmResult . head

-- | Execute a symbolic ':prove' or ':sat' command.
--
--   This command returns a pair: the first element is the name of the
--   solver that completes the given query (if any) along with the result
--   of executing the query.
satProve :: ProverCommand -> M.ModuleCmd (Maybe String, ProverResult)
satProve pc@ProverCommand {..} =
  protectStack proverError $ \(evo,modEnv) ->

  M.runModuleM (evo,modEnv) $ do

  M.io (prepareQuery evo modEnv pc) >>= \case
    Left msg -> return (Nothing, ProverError msg)
    Right (ts, q) ->
      do (firstProver, results) <- runProver pc q
         esatexprs <- processResults evo pc ts results
         return (firstProver, esatexprs)

-- | Execute a symbolic ':prove' or ':sat' command when the prover is
--   set to offline.  This only prepares the SMT input file for the
--   solver and does not actually invoke the solver.
--
--   This method returns either an error message or the text of
--   the SMT input file corresponding to the given prover command.
satProveOffline :: ProverCommand -> M.ModuleCmd (Either String String)
satProveOffline pc@ProverCommand {..} =
  protectStack (\msg (_,modEnv) -> return (Right (Left msg, modEnv), [])) $
  \(evOpts,modEnv) -> do
    let isSat = case pcQueryType of
          ProveQuery -> False
          SatQuery _ -> True

    prepareQuery evOpts modEnv pc >>= \case
      Left msg -> return (Right (Left msg, modEnv), [])
      Right (_ts, q) ->
        do smtlib <- SBV.generateSMTBenchmark isSat q
           return (Right (Right smtlib, modEnv), [])


protectStack :: (String -> M.ModuleCmd a)
             -> M.ModuleCmd a
             -> M.ModuleCmd a
protectStack mkErr cmd modEnv =
  X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg = "Symbolic evaluation failed to terminate."
        handler () = mkErr msg modEnv

-- | Given concrete values from the solver and a collection of finite types,
--   reconstruct Cryptol concrete values, and return any unused solver
--   values.
parseValues :: [FinType] -> [SBV.CV] -> ([Concrete.Value], [SBV.CV])
parseValues [] cvs = ([], cvs)
parseValues (t : ts) cvs = (v : vs, cvs'')
  where (v, cvs') = parseValue t cvs
        (vs, cvs'') = parseValues ts cvs'

-- | Parse a single value of a finite type by consuming some number of
--   solver values.  The parsed Cryptol values is returned along with
--   any solver values not consumed.
parseValue :: FinType -> [SBV.CV] -> (Concrete.Value, [SBV.CV])
parseValue FTBit [] = panic "Cryptol.Symbolic.parseValue" [ "empty FTBit" ]
parseValue FTBit (cv : cvs) = (Eval.VBit (SBV.cvToBool cv), cvs)
parseValue FTInteger cvs =
  case SBV.genParse SBV.KUnbounded cvs of
    Just (x, cvs') -> (Eval.VInteger x, cvs')
    Nothing        -> panic "Cryptol.Symbolic.parseValue" [ "no integer" ]
parseValue (FTIntMod _) cvs = parseValue FTInteger cvs
parseValue (FTSeq 0 FTBit) cvs = (Eval.word Concrete 0 0, cvs)
parseValue (FTSeq n FTBit) cvs =
  case SBV.genParse (SBV.KBounded False n) cvs of
    Just (x, cvs') -> (Eval.word Concrete (toInteger n) x, cvs')
    Nothing        -> (Eval.VWord (genericLength vs) (Eval.WordVal <$>
                         (Eval.packWord Concrete (map Eval.fromVBit vs))), cvs')
      where (vs, cvs') = parseValues (replicate n FTBit) cvs
parseValue (FTSeq n t) cvs =
                      (Eval.VSeq (toInteger n) $ Eval.finiteSeqMap Concrete (map Eval.ready vs)
                      , cvs'
                      )
  where (vs, cvs') = parseValues (replicate n t) cvs
parseValue (FTTuple ts) cvs = (Eval.VTuple (map Eval.ready vs), cvs')
  where (vs, cvs') = parseValues ts cvs
parseValue (FTRecord fs) cvs = (Eval.VRecord (Map.fromList (zip ns (map Eval.ready vs))), cvs')
  where (ns, ts)   = unzip (Map.toList fs)
        (vs, cvs') = parseValues ts cvs

inBoundsIntMod :: Integer -> Eval.SInteger SBV -> Eval.SBit SBV
inBoundsIntMod n x =
  let z  = SBV.svInteger SBV.KUnbounded 0
      n' = SBV.svInteger SBV.KUnbounded n
   in SBV.svAnd (SBV.svLessEq z x) (SBV.svLessThan x n')

forallFinType :: FinType -> WriterT [Eval.SBit SBV] SBV.Symbolic Value
forallFinType ty =
  case ty of
    FTBit         -> Eval.VBit <$> lift forallSBool_
    FTInteger     -> Eval.VInteger <$> lift forallSInteger_
    FTIntMod n    -> do x <- lift forallSInteger_
                        tell [inBoundsIntMod n x]
                        return (Eval.VInteger x)
    FTSeq 0 FTBit -> return $ Eval.word SBV 0 0
    FTSeq n FTBit -> Eval.VWord (toInteger n) . return . Eval.WordVal <$> lift (forallBV_ n)
    FTSeq n t     -> do vs <- replicateM n (forallFinType t)
                        return $ Eval.VSeq (toInteger n) $ Eval.finiteSeqMap SBV (map pure vs)
    FTTuple ts    -> Eval.VTuple <$> mapM (fmap pure . forallFinType) ts
    FTRecord fs   -> Eval.VRecord <$> mapM (fmap pure . forallFinType) fs

existsFinType :: FinType -> WriterT [Eval.SBit SBV] SBV.Symbolic Value
existsFinType ty =
  case ty of
    FTBit         -> Eval.VBit <$> lift existsSBool_
    FTInteger     -> Eval.VInteger <$> lift existsSInteger_
    FTIntMod n    -> do x <- lift existsSInteger_
                        tell [inBoundsIntMod n x]
                        return (Eval.VInteger x)
    FTSeq 0 FTBit -> return $ Eval.word SBV 0 0
    FTSeq n FTBit -> Eval.VWord (toInteger n) . return . Eval.WordVal <$> lift (existsBV_ n)
    FTSeq n t     -> do vs <- replicateM n (existsFinType t)
                        return $ Eval.VSeq (toInteger n) $ Eval.finiteSeqMap SBV (map pure vs)
    FTTuple ts    -> Eval.VTuple <$> mapM (fmap pure . existsFinType) ts
    FTRecord fs   -> Eval.VRecord <$> mapM (fmap pure . existsFinType) fs

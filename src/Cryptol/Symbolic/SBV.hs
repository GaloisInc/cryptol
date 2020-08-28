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
 ( SBVProverConfig
 , defaultProver
 , proverNames
 , setupProver
 , satProve
 , satProveOffline
 , SBVPortfolioException(..)
 ) where


import Control.Concurrent.Async
import Control.Monad.IO.Class
import Control.Monad (replicateM, when, zipWithM, foldM, forM_)
import Control.Monad.Writer (WriterT, runWriterT, tell, lift)
--import Data.List (genericLength)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Control.Exception as X
import System.Exit (ExitCode(ExitSuccess))

import LibBF(bfNaN)

import qualified Data.SBV as SBV (sObserve)
import qualified Data.SBV.Internals as SBV (SBV(..))
import qualified Data.SBV.Dynamic as SBV
import           Data.SBV (Timing(SaveTiming))

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M

import           Cryptol.TypeCheck.Solver.InfNat(Nat'(..))

import qualified Cryptol.Eval.Backend as Eval
import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Concrete.FloatHelpers as Concrete
import qualified Cryptol.Eval.Monad as Eval
import qualified Cryptol.Eval.Type as Eval
import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.SBV
import           Cryptol.Symbolic
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Logger(logPutStrLn)
import           Cryptol.Utils.RecordMap

import Prelude ()
import Prelude.Compat

doEval :: MonadIO m => Eval.Eval a -> m a
doEval m = liftIO $ Eval.runEval m

doSBVEval :: MonadIO m => SBVEval a -> m (SBV.SVal, a)
doSBVEval m =
  (liftIO $ Eval.runEval (sbvEval m)) >>= \case
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

newtype SBVPortfolioException
  = SBVPortfolioException [Either X.SomeException (Maybe String,String)]

instance Show SBVPortfolioException where
  show (SBVPortfolioException exs) =
       unlines ("All solvers in the portfolio failed!" : map f exs)
    where
    f (Left e) = X.displayException e
    f (Right (Nothing, msg)) = msg
    f (Right (Just nm, msg)) = nm ++ ": " ++ msg

instance X.Exception SBVPortfolioException

data SBVProverConfig
  = SBVPortfolio [SBV.SMTConfig]
  | SBVProverConfig SBV.SMTConfig

defaultProver :: SBVProverConfig
defaultProver = SBVProverConfig SBV.z3

-- | The names of all the solvers supported by SBV
proverNames :: [String]
proverNames = map fst proverConfigs

setupProver :: String -> IO (Either String ([String], SBVProverConfig))
setupProver nm
  | nm `elem` ["any","sbv-any"] =
    do ps <- SBV.sbvAvailableSolvers
       case ps of
         [] -> pure (Left "SBV could not find any provers")
         _ ->  let msg = "SBV found the following solvers: " ++ show (map (SBV.name . SBV.solver) ps) in
               pure (Right ([msg], SBVPortfolio ps))

    -- special case, we search for two different yices binaries
  | nm `elem` ["yices","sbv-yices"] = tryCfgs SBV.yices ["yices-smt2", "yices_smt2"]

  | otherwise =
    case lookup nm proverConfigs of
      Just cfg -> tryCfgs cfg []
      Nothing  -> pure (Left ("unknown solver name: " ++ nm))

  where
  tryCfgs cfg (e:es) =
    do let cfg' = cfg{ SBV.solver = (SBV.solver cfg){ SBV.executable = e } }
       ok <- SBV.sbvCheckSolverInstallation cfg'
       if ok then pure (Right ([], SBVProverConfig cfg')) else tryCfgs cfg es

  tryCfgs cfg [] =
    do ok <- SBV.sbvCheckSolverInstallation cfg
       pure (Right (ws ok, SBVProverConfig cfg))

  ws ok = if ok then [] else notFound
  notFound = ["Warning: " ++ nm ++ " installation not found"]

satSMTResults :: SBV.SatResult -> [SBV.SMTResult]
satSMTResults (SBV.SatResult r) = [r]

allSatSMTResults :: SBV.AllSatResult -> [SBV.SMTResult]
allSatSMTResults (SBV.AllSatResult (_, _, _, rs)) = rs

thmSMTResults :: SBV.ThmResult -> [SBV.SMTResult]
thmSMTResults (SBV.ThmResult r) = [r]

proverError :: String -> M.ModuleCmd (Maybe String, ProverResult)
proverError msg (_, _, modEnv) =
  return (Right ((Nothing, ProverError msg), modEnv), [])


isFailedResult :: [SBV.SMTResult] -> Maybe String
isFailedResult [] = Just "Solver returned no results!"
isFailedResult (r:_) =
  case r of
    SBV.Unknown _cfg rsn  -> Just ("Solver returned UNKNOWN " ++ show rsn)
    SBV.ProofError _ ms _ -> Just (unlines ("Solver error" : ms))
    _ -> Nothing

runSingleProver ::
  ProverCommand ->
  (String -> IO ()) ->
  SBV.SMTConfig ->
  (SBV.SMTConfig -> SBV.Symbolic SBV.SVal -> IO res) ->
  (res -> [SBV.SMTResult]) ->
  SBV.Symbolic SBV.SVal ->
  IO (Maybe String, [SBV.SMTResult])
runSingleProver ProverCommand{..} lPutStrLn prover callSolver processResult e = do
   when pcVerbose $
     lPutStrLn $ "Trying proof with " ++
                               show (SBV.name (SBV.solver prover))
   res <- callSolver prover e

   when pcVerbose $
     lPutStrLn $ "Got result from " ++
                               show (SBV.name (SBV.solver prover))
   return (Just (show (SBV.name (SBV.solver prover))), processResult res)

runMultiProvers ::
  ProverCommand ->
  (String -> IO ()) ->
  [SBV.SMTConfig] ->
  (SBV.SMTConfig -> SBV.Symbolic SBV.SVal -> IO res) ->
  (res -> [SBV.SMTResult]) ->
  SBV.Symbolic SBV.SVal ->
  IO (Maybe String, [SBV.SMTResult])
runMultiProvers pc lPutStrLn provers callSolver processResult e = do
  as <- mapM async [ runSingleProver pc lPutStrLn p callSolver processResult e
                   | p <- provers
                   ]
  waitForResults [] as

 where
 waitForResults exs [] = X.throw (SBVPortfolioException exs)
 waitForResults exs as =
   do (winner, result) <- waitAnyCatch as
      let others = filter (/= winner) as
      case result of
        Left ex ->
          waitForResults (Left ex:exs) others
        Right r@(nm, rs)
          | Just msg <- isFailedResult rs ->
              waitForResults (Right (nm, msg) : exs) others
          | otherwise ->
              do forM_ others (\a -> X.throwTo (asyncThreadId a) ExitSuccess)
                 return r

-- | Select the appropriate solver or solvers from the given prover command,
--   and invoke those solvers on the given symbolic value.
runProver :: SBVProverConfig -> ProverCommand -> (String -> IO ()) -> SBV.Symbolic SBV.SVal -> IO (Maybe String, [SBV.SMTResult])
runProver proverConfig pc@ProverCommand{..} lPutStrLn x =
  do let mSatNum = case pcQueryType of
                     SatQuery (SomeSat n) -> Just n
                     SatQuery AllSat -> Nothing
                     ProveQuery -> Nothing
                     SafetyQuery -> Nothing

     case proverConfig of
       SBVPortfolio ps -> 
         let ps' = [ p { SBV.transcript = pcSmtFile
                       , SBV.timing = SaveTiming pcProverStats
                       , SBV.verbose = pcVerbose
                       , SBV.validateModel = pcValidate
                       }
                   | p <- ps
                   ] in

          case pcQueryType of
            ProveQuery  -> runMultiProvers pc lPutStrLn ps' SBV.proveWith thmSMTResults x
            SafetyQuery -> runMultiProvers pc lPutStrLn ps' SBV.proveWith thmSMTResults x
            SatQuery (SomeSat 1) -> runMultiProvers pc lPutStrLn ps' SBV.satWith satSMTResults x
            _ -> return (Nothing,
                   [SBV.ProofError p
                     [":sat with option prover=any requires option satNum=1"]
                     Nothing
                   | p <- ps])

       SBVProverConfig p ->
         let p' = p { SBV.transcript = pcSmtFile
                    , SBV.allSatMaxModelCount = mSatNum
                    , SBV.timing = SaveTiming pcProverStats
                    , SBV.verbose = pcVerbose
                    , SBV.validateModel = pcValidate
                    } in
          case pcQueryType of
            ProveQuery  -> runSingleProver pc lPutStrLn p' SBV.proveWith thmSMTResults x
            SafetyQuery -> runSingleProver pc lPutStrLn p' SBV.proveWith thmSMTResults x
            SatQuery (SomeSat 1) -> runSingleProver pc lPutStrLn p' SBV.satWith satSMTResults x
            SatQuery _           -> runSingleProver pc lPutStrLn p' SBV.allSatWith allSatSMTResults x


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
           SafetyQuery -> forallFinType

     -- The `addAsm` function is used to combine assumptions that
     -- arise from the types of symbolic variables (e.g. Z n values
     -- are assumed to be integers in the range `0 <= x < n`) with
     -- the main content of the query.  We use conjunction or implication
     -- depending on the type of query.
     let addAsm = case pcQueryType of
           ProveQuery  -> \x y -> SBV.svOr (SBV.svNot x) y
           SafetyQuery -> \x y -> SBV.svOr (SBV.svNot x) y
           SatQuery _ -> \x y -> SBV.svAnd x y

     let tbl = primTable
     let ?evalPrim = \i -> Map.lookup i tbl
     case predArgTypes pcQueryType pcSchema of
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
                 (safety,b) <- doSBVEval $
                     do env <- Eval.evalDecls SBV extDgs mempty
                        v <- Eval.evalExpr SBV env pcExpr
                        appliedVal <- foldM Eval.fromVFun v (map pure args)
                        case pcQueryType of
                          SafetyQuery ->
                            do _ <- Eval.forceValue SBV appliedVal
                               pure SBV.svTrue
                          _ -> pure (Eval.fromVBit appliedVal)

                 -- Ignore the safety condition if the flag is set and we are not
                 -- doing a safety query
                 let safety' = case pcQueryType of
                                 SafetyQuery -> safety
                                 _ | pcIgnoreSafety -> SBV.svTrue
                                   | otherwise -> safety

                 -- "observe" the value of the safety predicate.  This makes its value
                 -- avaliable in the resulting model.
                 SBV.sObserve "safety" (SBV.SBV safety' :: SBV.SBV Bool)

                 return (foldr addAsm (SBV.svAnd safety' b) asms))


-- | Turn the SMT results from SBV into a @ProverResult@ that is ready for the Cryptol REPL.
--   There may be more than one result if we made a multi-sat query.
processResults ::
  ProverCommand ->
  [FinType] {- ^ Types of the symbolic inputs -} ->
  [SBV.SMTResult] {- ^ Results from the solver -} ->
  M.ModuleT IO ProverResult
processResults ProverCommand{..} ts results =
 do let isSat = case pcQueryType of
          ProveQuery -> False
          SafetyQuery -> False
          SatQuery _ -> True

    prims <- M.getPrimMap

    case results of
       -- allSat can return more than one as long as
       -- they're satisfiable
       (SBV.Satisfiable {} : _) | isSat -> do
         tevss <- map snd <$> mapM (mkTevs prims) results
         return $ AllSatResult tevss

       -- prove should only have one counterexample
       [r@SBV.Satisfiable{}] -> do
         (safety, res) <- mkTevs prims r
         let cexType = if safety then PredicateFalsified else SafetyViolation
         return $ CounterExample cexType res

       -- prove returns only one
       [SBV.Unsatisfiable {}] ->
         return $ ThmResult (unFinType <$> ts)

       -- unsat returns empty
       [] -> return $ ThmResult (unFinType <$> ts)

       -- otherwise something is wrong
       _ -> return $ ProverError (rshow results)
              where rshow | isSat = show .  SBV.AllSatResult . (False,False,False,)
                          | otherwise = show . SBV.ThmResult . head

  where
  mkTevs prims result = do
    -- It's a bit fragile, but the value of the safety predicate seems
    -- to always be the first value in the model assignment list.
    let Right (_, (safetyCV : cvs)) = SBV.getModelAssignment result
        safety = SBV.cvToBool safetyCV
        (vs, _) = parseValues ts cvs
        sattys = unFinType <$> ts
    satexprs <-
      doEval (zipWithM (Concrete.toExpr prims) sattys vs)
    case zip3 sattys <$> (sequence satexprs) <*> pure vs of
      Nothing ->
        panic "Cryptol.Symbolic.sat"
          [ "unable to make assignment into expression" ]
      Just tevs -> return $ (safety, tevs)


-- | Execute a symbolic ':prove' or ':sat' command.
--
--   This command returns a pair: the first element is the name of the
--   solver that completes the given query (if any) along with the result
--   of executing the query.
satProve :: SBVProverConfig -> ProverCommand -> M.ModuleCmd (Maybe String, ProverResult)
satProve proverCfg pc@ProverCommand {..} =
  protectStack proverError $ \(evo, byteReader, modEnv) ->

  M.runModuleM (evo, byteReader, modEnv) $ do

  let lPutStrLn = logPutStrLn (Eval.evalLogger evo)

  M.io (prepareQuery evo modEnv pc) >>= \case
    Left msg -> return (Nothing, ProverError msg)
    Right (ts, q) ->
      do (firstProver, results) <- M.io (runProver proverCfg pc lPutStrLn q)
         esatexprs <- processResults pc ts results
         return (firstProver, esatexprs)

-- | Execute a symbolic ':prove' or ':sat' command when the prover is
--   set to offline.  This only prepares the SMT input file for the
--   solver and does not actually invoke the solver.
--
--   This method returns either an error message or the text of
--   the SMT input file corresponding to the given prover command.
satProveOffline :: SBVProverConfig -> ProverCommand -> M.ModuleCmd (Either String String)
satProveOffline _proverCfg pc@ProverCommand {..} =
  protectStack (\msg (_,_,modEnv) -> return (Right (Left msg, modEnv), [])) $
  \(evOpts, _, modEnv) -> do
    let isSat = case pcQueryType of
          ProveQuery -> False
          SafetyQuery -> False
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
parseValue FTRational cvs =
  fromMaybe (panic "Cryptol.Symbolic.parseValue" ["no rational"]) $
  do (n,cvs')  <- SBV.genParse SBV.KUnbounded cvs
     (d,cvs'') <- SBV.genParse SBV.KUnbounded cvs'
     return (Eval.VRational (Eval.SRational n d), cvs'')
parseValue (FTSeq 0 FTBit) cvs = (Concrete.mkWord (Concrete.mkBv 0 0), cvs)
parseValue (FTSeq n FTBit) cvs =
  case SBV.genParse (SBV.KBounded False n) cvs of
    Just (x, cvs') -> (Concrete.mkWord (Concrete.mkBv (toInteger n) x), cvs')
    Nothing        -> (Concrete.mkWord (Concrete.packBits (map Eval.fromVBit vs)), cvs')
      where (vs, cvs') = parseValues (replicate n FTBit) cvs
parseValue (FTSeq n t) cvs =
                      (Eval.VSeq (Nat (toInteger n)) (finTypeValue t) $
                          Eval.finiteSeqMap' (map Eval.ready vs)
                      , cvs'
                      )
  where (vs, cvs') = parseValues (replicate n t) cvs
parseValue (FTTuple ts) cvs = (Eval.VTuple (map Eval.ready vs), cvs')
  where (vs, cvs') = parseValues ts cvs
parseValue (FTRecord r) cvs = (Eval.VRecord r', cvs')
  where (ns, ts)   = unzip $ canonicalFields r
        (vs, cvs') = parseValues ts cvs
        fs         = zip ns (map Eval.ready vs)
        r'         = recordFromFieldsWithDisplay (displayOrder r) fs

parseValue (FTFloat e p) cvs =
   (Eval.VFloat Concrete.BF { Concrete.bfValue = bfNaN
                            , Concrete.bfExpWidth = e
                            , Concrete.bfPrecWidth = p
                            }
   , cvs
   )
   -- XXX: NOT IMPLEMENTED

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
    FTRational    ->
      do n <- lift forallSInteger_
         d <- lift forallSInteger_
         let z = SBV.svInteger SBV.KUnbounded 0
         tell [SBV.svLessThan z d]
         return (Eval.VRational (Eval.SRational n d))
    FTFloat {}    -> pure (Eval.VFloat ()) -- XXX: NOT IMPLEMENTED
    FTIntMod n    -> do x <- lift forallSInteger_
                        tell [inBoundsIntMod n x]
                        return (Eval.VInteger x)
    FTSeq 0 FTBit -> pure $ Eval.VSeq (Nat 0) Eval.TVBit (Eval.voidSeqMap)
    FTSeq n FTBit -> Eval.VSeq (Nat (toInteger n)) Eval.TVBit . Eval.unpackSeqMap' <$> lift (forallBV_ n)
    FTSeq n t     -> do vs <- replicateM n (forallFinType t)
                        return $ Eval.VSeq (Nat (toInteger n)) (finTypeValue t) $
                          Eval.finiteSeqMap' (map pure vs)
    FTTuple ts    -> Eval.VTuple <$> mapM (fmap pure . forallFinType) ts
    FTRecord fs   -> Eval.VRecord <$> traverse (fmap pure . forallFinType) fs

existsFinType :: FinType -> WriterT [Eval.SBit SBV] SBV.Symbolic Value
existsFinType ty =
  case ty of
    FTBit         -> Eval.VBit <$> lift existsSBool_
    FTInteger     -> Eval.VInteger <$> lift existsSInteger_
    FTRational    ->
      do n <- lift existsSInteger_
         d <- lift existsSInteger_
         let z = SBV.svInteger SBV.KUnbounded 0
         tell [SBV.svLessThan z d]
         return (Eval.VRational (Eval.SRational n d))
    FTFloat {}    -> pure $ Eval.VFloat () -- XXX: NOT IMPLEMENTED
    FTIntMod n    -> do x <- lift existsSInteger_
                        tell [inBoundsIntMod n x]
                        return (Eval.VInteger x)
    FTSeq 0 FTBit -> pure $ Eval.VSeq (Nat 0) Eval.TVBit Eval.voidSeqMap
    FTSeq n FTBit -> Eval.VSeq (Nat (toInteger n)) Eval.TVBit . Eval.unpackSeqMap' <$> lift (existsBV_ n)
    FTSeq n t     -> do vs <- replicateM n (existsFinType t)
                        return $ Eval.VSeq (Nat (toInteger n)) (finTypeValue t) $
                          Eval.finiteSeqMap' (map pure vs)
    FTTuple ts    -> Eval.VTuple <$> mapM (fmap pure . existsFinType) ts
    FTRecord fs   -> Eval.VRecord <$> traverse (fmap pure . existsFinType) fs

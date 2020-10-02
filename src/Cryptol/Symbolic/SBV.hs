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


import Control.Applicative
import Control.Concurrent.Async
import Control.Concurrent.MVar
import Control.Monad.IO.Class
import Control.Monad (when, foldM, forM_)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Control.Exception as X
import System.Exit (ExitCode(ExitSuccess))

import LibBF(bfNaN)

import qualified Data.SBV as SBV (sObserve, symbolicEnv)
import qualified Data.SBV.Internals as SBV (SBV(..))
import qualified Data.SBV.Dynamic as SBV
import           Data.SBV (Timing(SaveTiming))

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M
import qualified Cryptol.ModuleSystem.Name as M

import           Cryptol.Backend.SBV
import qualified Cryptol.Backend.FloatHelpers as FH

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.SBV
import           Cryptol.Symbolic
import           Cryptol.TypeCheck.AST
import           Cryptol.Utils.Ident (preludeReferenceName, prelPrim, identText)
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Logger(logPutStrLn)
import           Cryptol.Utils.RecordMap


import Prelude ()
import Prelude.Compat

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
runProver ::
  SBVProverConfig ->
  ProverCommand ->
  (String -> IO ()) ->
  SBV.Symbolic SBV.SVal ->
  IO (Maybe String, [SBV.SMTResult])
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
  ProverCommand ->
  M.ModuleT IO (Either String ([FinType], SBV.Symbolic SBV.SVal))
prepareQuery evo ProverCommand{..} =
  do ds <- do (_mp, m) <- M.loadModuleFrom (M.FromModule preludeReferenceName)
              let decls = mDecls m
              let nms = fst <$> Map.toList (M.ifDecls (M.ifPublic (M.genIface m)))
              let ds = Map.fromList [ (prelPrim (identText (M.nameIdent nm)), EWhere (EVar nm) decls) | nm <- nms ]
              pure ds

     modEnv <- M.getModuleEnv
     let extDgs = M.allDeclGroups modEnv ++ pcExtraDecls

     -- The `addAsm` function is used to combine assumptions that
     -- arise from the types of symbolic variables (e.g. Z n values
     -- are assumed to be integers in the range `0 <= x < n`) with
     -- the main content of the query.  We use conjunction or implication
     -- depending on the type of query.
     let addAsm = case pcQueryType of
           ProveQuery  -> \x y -> SBV.svOr (SBV.svNot x) y
           SafetyQuery -> \x y -> SBV.svOr (SBV.svNot x) y
           SatQuery _ -> \x y -> SBV.svAnd x y

     case predArgTypes pcQueryType pcSchema of
       Left msg -> return (Left msg)
       Right ts -> M.io $
         do when pcVerbose $ logPutStrLn (Eval.evalLogger evo) "Simulating..."
            pure $ Right $ (ts,
              do sbvState <- SBV.symbolicEnv
                 stateMVar <- liftIO (newMVar sbvState)
                 defRelsVar <- liftIO (newMVar SBV.svTrue)
                 let sym = SBV stateMVar defRelsVar
                 let tbl = primTable sym
                 let ?evalPrim = \i -> (Right <$> Map.lookup i tbl) <|>
                                       (Left <$> Map.lookup i ds)
                 -- Compute the symbolic inputs, and any domain constraints needed
                 -- according to their types.
                 args <- map (pure . varShapeToValue sym) <$>
                     liftIO (mapM (freshVar (sbvFreshFns sym)) ts)
                 -- Run the main symbolic computation.  First we populate the
                 -- evaluation environment, then we compute the value, finally
                 -- we apply it to the symbolic inputs.
                 (safety,b) <- doSBVEval $
                     do env <- Eval.evalDecls sym extDgs mempty
                        v <- Eval.evalExpr sym env pcExpr
                        appliedVal <- foldM Eval.fromVFun v args
                        case pcQueryType of
                          SafetyQuery ->
                            do Eval.forceValue appliedVal
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

                 -- read any definitional relations that were asserted
                 defRels <- liftIO (readMVar defRelsVar)

                 return (addAsm defRels (SBV.svAnd safety' b)))

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
        (vs, []) = parseValues ts cvs
        mdl = computeModel prims ts vs
    return (safety, mdl)


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

  prepareQuery evo pc >>= \case
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
  \(evo, byteReader, modEnv) -> M.runModuleM (evo,byteReader,modEnv) $
     do let isSat = case pcQueryType of
              ProveQuery -> False
              SafetyQuery -> False
              SatQuery _ -> True

        prepareQuery evo pc >>= \case
          Left msg -> return (Left msg)
          Right (_ts, q) -> Right <$> M.io (SBV.generateSMTBenchmark isSat q)

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
parseValues :: [FinType] -> [SBV.CV] -> ([VarShape Concrete.Concrete], [SBV.CV])
parseValues [] cvs = ([], cvs)
parseValues (t : ts) cvs = (v : vs, cvs'')
  where (v, cvs') = parseValue t cvs
        (vs, cvs'') = parseValues ts cvs'

-- | Parse a single value of a finite type by consuming some number of
--   solver values.  The parsed Cryptol values is returned along with
--   any solver values not consumed.
parseValue :: FinType -> [SBV.CV] -> (VarShape Concrete.Concrete, [SBV.CV])
parseValue FTBit [] = panic "Cryptol.Symbolic.parseValue" [ "empty FTBit" ]
parseValue FTBit (cv : cvs) = (VarBit (SBV.cvToBool cv), cvs)
parseValue FTInteger cvs =
  case SBV.genParse SBV.KUnbounded cvs of
    Just (x, cvs') -> (VarInteger x, cvs')
    Nothing        -> panic "Cryptol.Symbolic.parseValue" [ "no integer" ]
parseValue (FTIntMod _) cvs = parseValue FTInteger cvs
parseValue FTRational cvs =
  fromMaybe (panic "Cryptol.Symbolic.parseValue" ["no rational"]) $
  do (n,cvs')  <- SBV.genParse SBV.KUnbounded cvs
     (d,cvs'') <- SBV.genParse SBV.KUnbounded cvs'
     return (VarRational n d, cvs'')
parseValue (FTSeq 0 FTBit) cvs = (VarWord (Concrete.mkBv 0 0), cvs)
parseValue (FTSeq n FTBit) cvs =
  case SBV.genParse (SBV.KBounded False n) cvs of
    Just (x, cvs') -> (VarWord (Concrete.mkBv (toInteger n) x), cvs')
    Nothing -> panic "Cryptol.Symbolic.parseValue" ["no bitvector"]
parseValue (FTSeq n t) cvs = (VarFinSeq (toInteger n) vs, cvs')
  where (vs, cvs') = parseValues (replicate n t) cvs
parseValue (FTTuple ts) cvs = (VarTuple vs, cvs')
  where (vs, cvs') = parseValues ts cvs
parseValue (FTRecord r) cvs = (VarRecord r', cvs')
  where (ns, ts)   = unzip $ canonicalFields r
        (vs, cvs') = parseValues ts cvs
        fs         = zip ns vs
        r'         = recordFromFieldsWithDisplay (displayOrder r) fs

parseValue (FTFloat e p) cvs =
   (VarFloat FH.BF { FH.bfValue = bfNaN
                   , FH.bfExpWidth = e
                   , FH.bfPrecWidth = p
                   }
   , cvs
   )
   -- XXX: NOT IMPLEMENTED


freshBoundedInt :: SBV -> Maybe Integer -> Maybe Integer -> IO SBV.SVal
freshBoundedInt sym lo hi =
  do x <- freshSInteger_ sym
     case lo of
       Just l  -> addDefEqn sym (SBV.svLessEq (SBV.svInteger SBV.KUnbounded l) x)
       Nothing -> pure ()
     case hi of
       Just h  -> addDefEqn sym (SBV.svLessEq x (SBV.svInteger SBV.KUnbounded h))
       Nothing -> pure ()
     return x

sbvFreshFns :: SBV -> FreshVarFns SBV
sbvFreshFns sym =
  FreshVarFns
  { freshBitVar     = freshSBool_ sym
  , freshWordVar    = freshBV_ sym . fromInteger
  , freshIntegerVar = freshBoundedInt sym
  , freshFloatVar   = \_ _ -> return () -- TODO
  }

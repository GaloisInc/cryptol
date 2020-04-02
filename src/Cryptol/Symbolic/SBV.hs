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
import Cryptol.TypeCheck.AST
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
  ]

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

checkProverInstallation :: String -> IO Bool
checkProverInstallation s =
  do let prover = lookupProver s
     SBV.sbvCheckSolverInstallation prover

thmSMTResults :: SBV.ThmResult -> [SBV.SMTResult]
thmSMTResults (SBV.ThmResult r) = [r]

proverError :: String -> M.ModuleCmd (Maybe String, ProverResult)
proverError msg (_,modEnv) =
  return (Right ((Nothing, ProverError msg), modEnv), [])

satProve :: ProverCommand -> M.ModuleCmd (Maybe String, ProverResult)
satProve ProverCommand {..} =
  protectStack proverError $ \(evo,modEnv) ->

  M.runModuleM (evo,modEnv) $ do
  let (isSat, mSatNum) = case pcQueryType of
        ProveQuery -> (False, Nothing)
        SatQuery sn -> case sn of
          SomeSat n -> (True, Just n)
          AllSat    -> (True, Nothing)
  let extDgs = allDeclGroups modEnv ++ pcExtraDecls
  provers <-
    case pcProverName of
      "any" -> M.io SBV.sbvAvailableSolvers
      _ -> return [(lookupProver pcProverName) { SBV.transcript = pcSmtFile
                                               , SBV.allSatMaxModelCount = mSatNum
                                               }]


  let provers' = [ p { SBV.timing = SaveTiming pcProverStats
                     , SBV.verbose = pcVerbose
                     , SBV.validateModel = pcValidate
                     } | p <- provers ]
  let tyFn = if isSat then existsFinType else forallFinType
  let lPutStrLn = M.withLogger logPutStrLn
  let runProver fn tag e = do
        case provers of
          [prover] -> do
            when pcVerbose $
              lPutStrLn $ "Trying proof with " ++
                                        show (SBV.name (SBV.solver prover))
            res <- M.io (fn prover e)
            when pcVerbose $
              lPutStrLn $ "Got result from " ++
                                        show (SBV.name (SBV.solver prover))
            return (Just (show (SBV.name (SBV.solver prover))), tag res)
          _ ->
            return ( Nothing
                   , [ SBV.ProofError
                         prover
                         [":sat with option prover=any requires option satNum=1"]
                         Nothing
                     | prover <- provers ]
                   )
      runProvers fn tag e = do
        when pcVerbose $
          lPutStrLn $ "Trying proof with " ++
                  intercalate ", " (map (show . SBV.name . SBV.solver) provers)
        (firstProver, timeElapsed, res) <- M.io (fn provers' e)
        when pcVerbose $
          lPutStrLn $ "Got result from " ++ show firstProver ++
                                            ", time: " ++ showTDiff timeElapsed
        return (Just (show firstProver), tag res)
  let runFn = case pcQueryType of
        ProveQuery -> runProvers SBV.proveWithAny thmSMTResults
        SatQuery sn -> case sn of
          SomeSat 1 -> runProvers SBV.satWithAny satSMTResults
          _         -> runProver SBV.allSatWith allSatSMTResults
  let addAsm = case pcQueryType of
        ProveQuery -> \x y -> SBV.svOr (SBV.svNot x) y
        SatQuery _ -> \x y -> SBV.svAnd x y

  let ?evalPrim = evalPrim
  case predArgTypes pcSchema of
    Left msg -> return (Nothing, ProverError msg)
    Right ts -> do when pcVerbose $ lPutStrLn "Simulating..."
                   (_,v) <- doSBVEval evo $
                              do env <- Eval.evalDecls SBV extDgs mempty
                                 Eval.evalExpr SBV env pcExpr
                   prims <- M.getPrimMap
                   runRes <- runFn $ do
                               (args, asms) <- runWriterT (mapM tyFn ts)
                               (_,b) <- doSBVEval evo (Eval.fromVBit <$>
                                          foldM Eval.fromVFun v (map pure args))
                               return (foldr addAsm b asms)
                   let (firstProver, results) = runRes
                   esatexprs <- case results of
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
                   return (firstProver, esatexprs)

satProveOffline :: ProverCommand -> M.ModuleCmd (Either String String)
satProveOffline ProverCommand {..} =
  protectStack (\msg (_,modEnv) -> return (Right (Left msg, modEnv), [])) $
  \(evOpts,modEnv) -> do
    let isSat = case pcQueryType of
          ProveQuery -> False
          SatQuery _ -> True
    let extDgs = allDeclGroups modEnv ++ pcExtraDecls
    let tyFn = if isSat then existsFinType else forallFinType
    let addAsm = if isSat then SBV.svAnd else \x y -> SBV.svOr (SBV.svNot x) y
    let ?evalPrim = evalPrim
    case predArgTypes pcSchema of
      Left msg -> return (Right (Left msg, modEnv), [])
      Right ts ->
        do when pcVerbose $ logPutStrLn (Eval.evalLogger evOpts) "Simulating..."
           (_,v) <- doSBVEval evOpts $
                      do env <- Eval.evalDecls SBV extDgs mempty
                         Eval.evalExpr SBV env pcExpr
           smtlib <- SBV.generateSMTBenchmark isSat $ do
             (args, asms) <- runWriterT (mapM tyFn ts)
             (_,b) <- doSBVEval evOpts
                          (Eval.fromVBit <$> foldM Eval.fromVFun v (map pure args))
             return (foldr addAsm b asms)
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

parseValues :: [FinType] -> [SBV.CV] -> ([Concrete.Value], [SBV.CV])
parseValues [] cvs = ([], cvs)
parseValues (t : ts) cvs = (v : vs, cvs'')
  where (v, cvs') = parseValue t cvs
        (vs, cvs'') = parseValues ts cvs'

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
  where (ns, ts) = unzip fs
        (vs, cvs') = parseValues ts cvs

allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedNonParamModules

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
    FTRecord fs   -> Eval.VRecord <$> mapM (fmap pure . forallFinType) (Map.fromList fs)

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
    FTRecord fs   -> Eval.VRecord <$> mapM (fmap pure . existsFinType) (Map.fromList fs)

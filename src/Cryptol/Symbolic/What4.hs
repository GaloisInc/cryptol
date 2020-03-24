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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic.What4
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
import Data.IORef(IORef)
import qualified Control.Exception as X
import Data.Maybe (fromMaybe)

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.Eval.Concrete (Concrete(..))
import qualified Cryptol.Eval.Monad as Eval
import           Cryptol.Eval.Type (TValue(..), evalType)

import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.Env (GenEvalEnv(..))
import           Cryptol.Eval.What4
import           Cryptol.Symbolic
import           Cryptol.TypeCheck.AST
import           Cryptol.Utils.Ident (Ident)
import           Cryptol.Utils.PP
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Logger(logPutStrLn)

import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.GroundEval as W4
import qualified What4.SatResult as W4
import qualified What4.SWord as SW
import           What4.Solver
import qualified What4.Solver.Z3 as Z3
--import qualified What4.Solver.Yices as Yices
--import qualified What4.Solver.CVC4 as CVC4

import           Data.Parameterized.Nonce


import Prelude ()
import Prelude.Compat

import Data.Time (NominalDiffTime)

type EvalEnv sym = GenEvalEnv (What4 sym)

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
  [ ("cvc4"     , cvc4Adapter )
  , ("yices"    , yicesAdapter )
  , ("z3"       , z3Adapter )
  , ("boolector", boolectorAdapter )
{-
  , ("mathsat"  , SBV.mathSAT  )
  , ("abc"      , SBV.abc      )
  , ("offline"  , SBV.defaultSMTCfg )
  , ("any"      , SBV.defaultSMTCfg )
-}
  ]

proverNames :: [String]
proverNames = map fst proverConfigs

lookupProver :: String -> SolverAdapter st
lookupProver s =
  case lookup s proverConfigs of
    Just cfg -> cfg
    -- should be caught by UI for setting prover user variable
    Nothing  -> panic "Cryptol.Symbolic.What4" [ "invalid prover: " ++ s ]


checkProverInstallation :: String -> IO Bool
checkProverInstallation s =
  fail "TODO! What4 check solver installation"

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
    M.io (W4.extendConfig Z3.z3Options (W4.getConfiguration sym))
--    M.io (W4.extendConfig CV4.cvc4Options (W4.getConfiguration sym))
--    M.io (W4.extendConfig Yices.yicesOptions (W4.getConfiguration sym))


    let ?evalPrim = evalPrim sym
    case predArgTypes pcSchema of
      Left msg -> return (Nothing, ProverError msg)
      Right ts ->
         do when pcVerbose $ lPutStrLn "Simulating..."

            args <- liftIO $ mapM (freshVariable sym) ts

            (safety,b) <-
               liftIO $ doW4Eval sym evo $
                   do env <- Eval.evalDecls (What4 sym) extDgs mempty
                      v <- Eval.evalExpr (What4 sym) env pcExpr
                      Eval.fromVBit <$> foldM Eval.fromVFun v (map (pure . varToSymValue sym) args)

            query <- case pcQueryType of
                       ProveQuery -> liftIO (W4.notPred sym =<< W4.andPred sym safety b)
                       SatQuery (SomeSat 1) -> liftIO (W4.andPred sym safety b)
                       SatQuery n -> fail ("TODO! support multisat: " ++ show n)

            logData <-
                 flip M.withLogger () $ \lg () ->
                     pure $ defaultLogData
                       { logCallbackVerbose = \i msg -> when (i > 2) (logPutStrLn lg msg)
                       , logReason = "solver query"
                       }

            pres <- liftIO $ Z3.runZ3InOverride sym logData [query] $ \res ->
                case res of
                  W4.Unknown -> return (ProverError "Solver returned UNKNOWN")
                  W4.Unsat _ -> return (ThmResult (map unFinType ts))
                  W4.Sat (evalFn,_) ->
                    do model <- computeModel evo primMap evalFn ts args
                       return (AllSatResult [ model ])

            return (Just "Z3", pres)


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
             Nothing -> fail "panic! computeModel expr"
             Just e  -> pure e
     zs <- computeModel evo primMap evalFn ts vs
     return ((t',e,v'):zs)
computeModel _ _ _ _ _ = fail "panic! computeModel mismatch"


data VarShape sym
  = VarBit (W4.Pred sym)
  | VarInteger (W4.SymInteger sym)
  | VarWord (SW.SWord sym)
  | VarFinSeq Int [VarShape sym]
  | VarTuple [VarShape sym]
  | VarRecord (Map.Map Ident (VarShape sym))

freshVariable :: W4.IsSymExprBuilder sym => sym -> FinType -> IO (VarShape sym)
freshVariable sym ty =
  case ty of
    FTBit         -> VarBit      <$> W4.freshConstant sym W4.emptySymbol W4.BaseBoolRepr
    FTInteger     -> VarInteger  <$> W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
    FTIntMod 0    -> VarInteger  <$> W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr
    FTIntMod n    -> VarInteger  <$> W4.freshBoundedInt sym W4.emptySymbol (Just 0) (Just (n-1))
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
    VarFinSeq n vs ->
       do vs' <- mapM (varToConcreteValue evalFn) vs
          pure (Eval.VSeq (toInteger n) (Eval.finiteSeqMap Concrete.Concrete (map pure vs')))
    VarTuple vs ->
       do vs' <- mapM (varToConcreteValue evalFn) vs
          pure (Eval.VTuple (map pure vs'))
    VarRecord fs ->
       do fs' <- traverse (varToConcreteValue evalFn) fs
          pure (Eval.VRecord (fmap pure fs'))



{-
  let (isSat, mSatNum) = case pcQueryType of
        ProveQuery -> (False, Nothing)
        SatQuery sn -> case sn of
          SomeSat n -> (True, Just n)
          AllSat    -> (True, Nothing)

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
            return (Just (SBV.name (SBV.solver prover)), tag res)
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
        return (Just firstProver, tag res)
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
-}

satProveOffline :: ProverCommand -> M.ModuleCmd (Either String String)
satProveOffline ProverCommand {..} =
  protectStack (\msg (_,modEnv) -> return (Right (Left msg, modEnv), [])) $
  \(evOpts,modEnv) -> do
    fail "TODO! satProveOffline"
{-
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
-}

protectStack :: (String -> M.ModuleCmd a)
             -> M.ModuleCmd a
             -> M.ModuleCmd a
protectStack mkErr cmd modEnv =
  X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg = "Symbolic evaluation failed to terminate."
        handler () = mkErr msg modEnv

{-
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
-}
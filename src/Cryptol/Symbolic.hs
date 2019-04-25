-- |
-- Module      :  Cryptol.Symbolic
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic where

import Control.Monad.IO.Class
import Control.Monad (replicateM, when, zipWithM, foldM)
import Control.Monad.Writer (WriterT, runWriterT, tell, lift)
import Data.List (intercalate, genericLength)
import Data.IORef(IORef)
import qualified Control.Exception as X

import qualified Data.SBV.Dynamic as SBV
import           Data.SBV (Timing(SaveTiming))
import           Data.SBV.Internals (showTDiff)

import qualified Cryptol.ModuleSystem as M hiding (getPrimMap)
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Base as M
import qualified Cryptol.ModuleSystem.Monad as M

import Cryptol.Symbolic.Prims
import Cryptol.Symbolic.Value

import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Monad as Eval
import qualified Cryptol.Eval.Type as Eval
import qualified Cryptol.Eval.Value as Eval
import           Cryptol.Eval.Env (GenEvalEnv(..))
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Logger(logPutStrLn)

import Prelude ()
import Prelude.Compat

import Data.Time (NominalDiffTime)

type EvalEnv = GenEvalEnv SBool SWord


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
    Nothing  -> panic "Cryptol.Symbolic" [ "invalid prover: " ++ s ]

type SatResult = [(Type, Expr, Eval.Value)]

data SatNum = AllSat | SomeSat Int
  deriving (Show)

data QueryType = SatQuery SatNum | ProveQuery
  deriving (Show)

data ProverCommand = ProverCommand {
    pcQueryType :: QueryType
    -- ^ The type of query to run
  , pcProverName :: String
    -- ^ Which prover to use (one of the strings in 'proverConfigs')
  , pcVerbose :: Bool
    -- ^ Verbosity flag passed to SBV
  , pcValidate :: Bool
    -- ^ Model validation flag passed to SBV
  , pcProverStats :: !(IORef ProverStats)
    -- ^ Record timing information here
  , pcExtraDecls :: [DeclGroup]
    -- ^ Extra declarations to bring into scope for symbolic
    -- simulation
  , pcSmtFile :: Maybe FilePath
    -- ^ Optionally output the SMTLIB query to a file
  , pcExpr :: Expr
    -- ^ The typechecked expression to evaluate
  , pcSchema :: Schema
    -- ^ The 'Schema' of @pcExpr@
  }

type ProverStats = NominalDiffTime

-- | A prover result is either an error message, an empty result (eg
-- for the offline prover), a counterexample or a lazy list of
-- satisfying assignments.
data ProverResult = AllSatResult [SatResult] -- LAZY
                  | ThmResult    [Type]
                  | EmptyResult
                  | ProverError  String

satSMTResults :: SBV.SatResult -> [SBV.SMTResult]
satSMTResults (SBV.SatResult r) = [r]

allSatSMTResults :: SBV.AllSatResult -> [SBV.SMTResult]
allSatSMTResults (SBV.AllSatResult (_, _, _, rs)) = rs

thmSMTResults :: SBV.ThmResult -> [SBV.SMTResult]
thmSMTResults (SBV.ThmResult r) = [r]

proverError :: String -> M.ModuleCmd (Maybe SBV.Solver, ProverResult)
proverError msg (_,modEnv) =
  return (Right ((Nothing, ProverError msg), modEnv), [])

satProve :: ProverCommand -> M.ModuleCmd (Maybe SBV.Solver, ProverResult)
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
  let doEval :: MonadIO m => Eval.Eval a -> m a
      doEval m  = liftIO $ Eval.runEval evo m
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
  case predArgTypes pcSchema of
    Left msg -> return (Nothing, ProverError msg)
    Right ts -> do when pcVerbose $ lPutStrLn "Simulating..."
                   v <- doEval $ do env <- Eval.evalDecls extDgs mempty
                                    Eval.evalExpr env pcExpr
                   prims <- M.getPrimMap
                   runRes <- runFn $ do
                               (args, asms) <- runWriterT (mapM tyFn ts)
                               b <- doEval (fromVBit <$>
                                      foldM fromVFun v (map Eval.ready args))
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
                             doEval (zipWithM (Eval.toExpr prims) sattys vs)
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
    case predArgTypes pcSchema of
      Left msg -> return (Right (Left msg, modEnv), [])
      Right ts ->
        do when pcVerbose $ logPutStrLn (Eval.evalLogger evOpts) "Simulating..."
           v <- liftIO $ Eval.runEval evOpts $
                   do env <- Eval.evalDecls extDgs mempty
                      Eval.evalExpr env pcExpr
           smtlib <- SBV.generateSMTBenchmark isSat $ do
             (args, asms) <- runWriterT (mapM tyFn ts)
             b <- liftIO $ Eval.runEval evOpts
                        (fromVBit <$> foldM fromVFun v (map Eval.ready args))
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

parseValues :: [FinType] -> [SBV.CV] -> ([Eval.Value], [SBV.CV])
parseValues [] cvs = ([], cvs)
parseValues (t : ts) cvs = (v : vs, cvs'')
  where (v, cvs') = parseValue t cvs
        (vs, cvs'') = parseValues ts cvs'

parseValue :: FinType -> [SBV.CV] -> (Eval.Value, [SBV.CV])
parseValue FTBit [] = panic "Cryptol.Symbolic.parseValue" [ "empty FTBit" ]
parseValue FTBit (cv : cvs) = (Eval.VBit (SBV.cvToBool cv), cvs)
parseValue FTInteger cvs =
  case SBV.genParse SBV.KUnbounded cvs of
    Just (x, cvs') -> (Eval.VInteger x, cvs')
    Nothing        -> panic "Cryptol.Symbolic.parseValue" [ "no integer" ]
parseValue (FTIntMod _) cvs = parseValue FTInteger cvs
parseValue (FTSeq 0 FTBit) cvs = (Eval.word 0 0, cvs)
parseValue (FTSeq n FTBit) cvs =
  case SBV.genParse (SBV.KBounded False n) cvs of
    Just (x, cvs') -> (Eval.word (toInteger n) x, cvs')
    Nothing        -> (VWord (genericLength vs) $ return $ Eval.WordVal $
                         Eval.packWord (map fromVBit vs), cvs')
      where (vs, cvs') = parseValues (replicate n FTBit) cvs
parseValue (FTSeq n t) cvs =
                      (Eval.VSeq (toInteger n) $ Eval.finiteSeqMap (map Eval.ready vs)
                      , cvs'
                      )
  where (vs, cvs') = parseValues (replicate n t) cvs
parseValue (FTTuple ts) cvs = (Eval.VTuple (map Eval.ready vs), cvs')
  where (vs, cvs') = parseValues ts cvs
parseValue (FTRecord fs) cvs = (Eval.VRecord (zip ns (map Eval.ready vs)), cvs')
  where (ns, ts) = unzip fs
        (vs, cvs') = parseValues ts cvs

allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedNonParamModules

data FinType
    = FTBit
    | FTInteger
    | FTIntMod Integer
    | FTSeq Int FinType
    | FTTuple [FinType]
    | FTRecord [(Ident, FinType)]

numType :: Integer -> Maybe Int
numType n
  | 0 <= n && n <= toInteger (maxBound :: Int) = Just (fromInteger n)
  | otherwise = Nothing

finType :: TValue -> Maybe FinType
finType ty =
  case ty of
    Eval.TVBit            -> Just FTBit
    Eval.TVInteger        -> Just FTInteger
    Eval.TVIntMod n       -> Just (FTIntMod n)
    Eval.TVSeq n t        -> FTSeq <$> numType n <*> finType t
    Eval.TVTuple ts       -> FTTuple <$> traverse finType ts
    Eval.TVRec fields     -> FTRecord <$> traverse (traverseSnd finType) fields
    Eval.TVAbstract {}    -> Nothing
    _                     -> Nothing

unFinType :: FinType -> Type
unFinType fty =
  case fty of
    FTBit        -> tBit
    FTInteger    -> tInteger
    FTIntMod n   -> tIntMod (tNum n)
    FTSeq l ety  -> tSeq (tNum l) (unFinType ety)
    FTTuple ftys -> tTuple (unFinType <$> ftys)
    FTRecord fs  -> tRec (zip fns tys)
      where
        fns = fst <$> fs
        tys = unFinType . snd <$> fs

predArgTypes :: Schema -> Either String [FinType]
predArgTypes schema@(Forall ts ps ty)
  | null ts && null ps =
      case go <$> (Eval.evalType mempty ty) of
        Right (Just fts) -> Right fts
        _ -> Left $ "Not a valid predicate type:\n" ++ show (pp schema)
  | otherwise = Left $ "Not a monomorphic type:\n" ++ show (pp schema)
  where
    go :: TValue -> Maybe [FinType]
    go Eval.TVBit             = Just []
    go (Eval.TVFun ty1 ty2)   = (:) <$> finType ty1 <*> go ty2
    go _                      = Nothing

inBoundsIntMod :: Integer -> SInteger -> SBool
inBoundsIntMod n x =
  SBV.svAnd (SBV.svLessEq (Eval.integerLit 0) x) (SBV.svLessThan x (Eval.integerLit n))

forallFinType :: FinType -> WriterT [SBool] SBV.Symbolic Value
forallFinType ty =
  case ty of
    FTBit         -> VBit <$> lift forallSBool_
    FTInteger     -> VInteger <$> lift forallSInteger_
    FTIntMod n    -> do x <- lift forallSInteger_
                        tell [inBoundsIntMod n x]
                        return (VInteger x)
    FTSeq 0 FTBit -> return $ Eval.word 0 0
    FTSeq n FTBit -> VWord (toInteger n) . return . Eval.WordVal <$> lift (forallBV_ n)
    FTSeq n t     -> do vs <- replicateM n (forallFinType t)
                        return $ VSeq (toInteger n) $ Eval.finiteSeqMap (map Eval.ready vs)
    FTTuple ts    -> VTuple <$> mapM (fmap Eval.ready . forallFinType) ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd (fmap Eval.ready . forallFinType)) fs

existsFinType :: FinType -> WriterT [SBool] SBV.Symbolic Value
existsFinType ty =
  case ty of
    FTBit         -> VBit <$> lift existsSBool_
    FTInteger     -> VInteger <$> lift existsSInteger_
    FTIntMod n    -> do x <- lift existsSInteger_
                        tell [inBoundsIntMod n x]
                        return (VInteger x)
    FTSeq 0 FTBit -> return $ Eval.word 0 0
    FTSeq n FTBit -> VWord (toInteger n) . return . Eval.WordVal <$> lift (existsBV_ n)
    FTSeq n t     -> do vs <- replicateM n (existsFinType t)
                        return $ VSeq (toInteger n) $ Eval.finiteSeqMap (map Eval.ready vs)
    FTTuple ts    -> VTuple <$> mapM (fmap Eval.ready . existsFinType) ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd (fmap Eval.ready . existsFinType)) fs

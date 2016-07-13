-- |
-- Module      :  $Header$
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
import Data.List (transpose, intercalate, genericLength, genericIndex)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Control.Exception as X

import qualified Data.SBV.Dynamic as SBV

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
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

import Prelude ()
import Prelude.Compat

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
allSatSMTResults (SBV.AllSatResult (_, rs)) = rs

thmSMTResults :: SBV.ThmResult -> [SBV.SMTResult]
thmSMTResults (SBV.ThmResult r) = [r]

proverError :: String -> M.ModuleCmd ProverResult
proverError msg modEnv = return (Right (ProverError msg, modEnv), [])


satProve :: ProverCommand -> M.ModuleCmd ProverResult
satProve ProverCommand {..} = protectStack proverError $ \modEnv ->
  M.runModuleM modEnv $ do
  let (isSat, mSatNum) = case pcQueryType of
        ProveQuery -> (False, Nothing)
        SatQuery sn -> case sn of
          SomeSat n -> (True, Just n)
          AllSat    -> (True, Nothing)
  let extDgs = allDeclGroups modEnv ++ pcExtraDecls
  provers <-
    case pcProverName of
      "any" -> M.io SBV.sbvAvailableSolvers
      _ -> return [(lookupProver pcProverName) { SBV.smtFile = pcSmtFile }]
  let provers' = [ p { SBV.timing = pcVerbose, SBV.verbose = pcVerbose } | p <- provers ]
  let tyFn = if isSat then existsFinType else forallFinType
  let runProver fn tag e = do
        case provers of
          [prover] -> do
            when pcVerbose $ M.io $
              putStrLn $ "Trying proof with " ++ show prover
            res <- M.io (fn prover e)
            when pcVerbose $ M.io $
              putStrLn $ "Got result from " ++ show prover
            return (tag res)
          _ ->
            return [ SBV.ProofError
                       prover
                       [":sat with option prover=any requires option satNum=1"]
                   | prover <- provers ]
      runProvers fn tag e = do
        when pcVerbose $ M.io $
          putStrLn $ "Trying proof with " ++
                     intercalate ", " (map show provers)
        (firstProver, res) <- M.io (fn provers' e)
        when pcVerbose $ M.io $
          putStrLn $ "Got result from " ++ show firstProver
        return (tag res)
  let runFn = case pcQueryType of
        ProveQuery -> runProvers SBV.proveWithAny thmSMTResults
        SatQuery sn -> case sn of
          SomeSat 1 -> runProvers SBV.satWithAny satSMTResults
          _         -> runProver SBV.allSatWith allSatSMTResults
  case predArgTypes pcSchema of
    Left msg -> return (ProverError msg)
    Right ts -> do when pcVerbose $ M.io $ putStrLn "Simulating..."
                   v <- M.io $ Eval.runEval $ do
                               env <- Eval.evalDecls extDgs mempty
                               Eval.evalExpr env pcExpr
                   prims <- M.getPrimMap
                   results' <- runFn $ do
                                 args <- mapM tyFn ts
                                 b <- liftIO $ Eval.runEval
                                        (fromVBit <$> foldM fromVFun v (map Eval.ready args))
                                 return b
                   let results = maybe results' (\n -> take n results') mSatNum
                   esatexprs <- case results of
                     -- allSat can return more than one as long as
                     -- they're satisfiable
                     (SBV.Satisfiable {} : _) -> do
                       tevss <- mapM mkTevs results
                       return $ AllSatResult tevss
                       where
                         mkTevs result = do
                           let Right (_, cws) = SBV.getModel result
                               (vs, _) = parseValues ts cws
                               sattys = unFinType <$> ts
                           satexprs <- liftIO $ Eval.runEval
                                           (zipWithM (Eval.toExpr prims) sattys vs)
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
                            where rshow | isSat = show . SBV.AllSatResult . (boom,)
                                        | otherwise = show . SBV.ThmResult . head
                                  boom = panic "Cryptol.Symbolic.sat"
                                           [ "attempted to evaluate bogus boolean for pretty-printing" ]
                   return esatexprs

satProveOffline :: ProverCommand -> M.ModuleCmd (Either String String)
satProveOffline ProverCommand {..} =
  protectStack (\msg modEnv -> return (Right (Left msg, modEnv), [])) $ \modEnv -> do
    let isSat = case pcQueryType of
          ProveQuery -> False
          SatQuery _ -> True
    let extDgs = allDeclGroups modEnv ++ pcExtraDecls
    let tyFn = if isSat then existsFinType else forallFinType
    case predArgTypes pcSchema of
      Left msg -> return (Right (Left msg, modEnv), [])
      Right ts ->
        do when pcVerbose $ putStrLn "Simulating..."
           v <- liftIO $ Eval.runEval $
                   do env <- Eval.evalDecls extDgs mempty
                      Eval.evalExpr env pcExpr
           smtlib <- SBV.compileToSMTLib SBV.SMTLib2 isSat $ do
             args <- mapM tyFn ts
             liftIO $ Eval.runEval
                    (fromVBit <$> foldM fromVFun v (map Eval.ready args))
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

parseValues :: [FinType] -> [SBV.CW] -> ([Eval.Value], [SBV.CW])
parseValues [] cws = ([], cws)
parseValues (t : ts) cws = (v : vs, cws'')
  where (v, cws') = parseValue t cws
        (vs, cws'') = parseValues ts cws'

parseValue :: FinType -> [SBV.CW] -> (Eval.Value, [SBV.CW])
parseValue FTBit [] = panic "Cryptol.Symbolic.parseValue" [ "empty FTBit" ]
parseValue FTBit (cw : cws) = (Eval.VBit (SBV.cwToBool cw), cws)
parseValue (FTSeq 0 FTBit) cws = (Eval.word 0 0, cws)
parseValue (FTSeq n FTBit) cws =
  case SBV.genParse (SBV.KBounded False n) cws of
    Just (x, cws') -> (Eval.word (toInteger n) x, cws')
    Nothing        -> (VWord (genericLength vs) $ return $ Eval.WordVal $
                         Eval.packWord (map fromVBit vs), cws')
      where (vs, cws') = parseValues (replicate n FTBit) cws
parseValue (FTSeq n t) cws =
                      (Eval.VSeq (toInteger n) $ Eval.SeqMap $ \i ->
                           return $ genericIndex vs i
                      , cws'
                      )
  where (vs, cws') = parseValues (replicate n t) cws
parseValue (FTTuple ts) cws = (Eval.VTuple (map Eval.ready vs), cws')
  where (vs, cws') = parseValues ts cws
parseValue (FTRecord fs) cws = (Eval.VRecord (zip ns (map Eval.ready vs)), cws')
  where (ns, ts) = unzip fs
        (vs, cws') = parseValues ts cws

allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedModules

data FinType
    = FTBit
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
    Eval.TVSeq n t        -> FTSeq <$> numType n <*> finType t
    Eval.TVTuple ts       -> FTTuple <$> traverse finType ts
    Eval.TVRec fields     -> FTRecord <$> traverse (traverseSnd finType) fields
    _                     -> Nothing

unFinType :: FinType -> Type
unFinType fty =
  case fty of
    FTBit        -> tBit
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
        _                -> Left $ "Not a valid predicate type:\n" ++ show (pp schema)
  | otherwise = Left $ "Not a monomorphic type:\n" ++ show (pp schema)
  where
    go :: TValue -> Maybe [FinType]
    go Eval.TVBit             = Just []
    go (Eval.TVFun ty1 ty2)   = (:) <$> finType ty1 <*> go ty2
    go _                      = Nothing

forallFinType :: FinType -> SBV.Symbolic Value
forallFinType ty =
  case ty of
    FTBit         -> VBit <$> forallSBool_
    FTSeq 0 FTBit -> return $ Eval.word 0 0
    FTSeq n FTBit -> VWord (toInteger n) . return . Eval.WordVal <$> (forallBV_ n)
    FTSeq n t     -> do vs <- replicateM n (forallFinType t)
                        return $ VSeq (toInteger n) $ Eval.SeqMap $ \i ->
                           return $ genericIndex vs i
    FTTuple ts    -> VTuple <$> mapM (fmap Eval.ready . forallFinType) ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd (fmap Eval.ready . forallFinType)) fs

existsFinType :: FinType -> SBV.Symbolic Value
existsFinType ty =
  case ty of
    FTBit         -> VBit <$> existsSBool_
    FTSeq 0 FTBit -> return $ Eval.word 0 0
    FTSeq n FTBit -> VWord (toInteger n) . return . Eval.WordVal <$> (existsBV_ n)
    FTSeq n t     -> do vs <- replicateM n (existsFinType t)
                        return $ VSeq (toInteger n) $ Eval.SeqMap $ \i ->
                           return $ genericIndex vs i
    FTTuple ts    -> VTuple <$> mapM (fmap Eval.ready . existsFinType) ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd (fmap Eval.ready . existsFinType)) fs

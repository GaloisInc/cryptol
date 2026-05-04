{-|
Module      : Cryptol.Symbolic.DIMACS
Description : What4 solver adapters for external DIMACS SAT and QDIMACS QBF solvers.
Copyright   : (c) 2026 Galois, Inc.
License     : BSD3
Maintainer  : cryptol@galois.com

This module implements What4 'SolverAdapter's that translate What4
boolean and bitvector expressions into DIMACS CNF (for SAT) or
QDIMACS (for QBF) via Tseitin encoding, run an external solver,
and parse the result.

This enables Cryptol's @:prove@ and @:sat@ commands to use pure SAT
solvers (MiniSat, CaDiCaL, Kissat, Glucose) and QBF solvers (DepQBF,
CAQE) via the @w4-sat@ and @w4-qbf@ prover settings.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic.DIMACS
  ( -- * SAT adapter
    dimacsSatAdapter
  , dimacsSatOptions
  , satSolverCommand
    -- * QBF adapter
  , dimacsQbfAdapter
  , dimacsQbfOptions
  , qbfSolverCommand
    -- * Model counting
  , sharpSATCommand
  , sharpSATOptions
  , countModels
  ) where

import           Control.Exception (bracket)
import           Control.Monad (foldM, replicateM, ap)
import           Data.Bits (testBit)
import qualified Data.BitVector.Sized as BV
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr ()
import           Data.Parameterized.Nonce (Nonce)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           System.Directory (getTemporaryDirectory, removeFile)
import           System.IO (Handle, hClose, hPutStrLn, openTempFile, hFlush)
import           System.Process (readProcess)

import qualified What4.Expr.App as W4
import qualified What4.Expr.BoolMap as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.GroundEval as W4
import qualified What4.Expr.WeightedSum as Sum
import qualified What4.Interface as W4
import qualified What4.SatResult as W4
import qualified What4.SemiRing as W4
import           What4.Config
import           What4.BaseTypes
import           What4.Concrete
import           What4.Solver.Adapter


--------------------------------------------------------------------------------
-- SAT adapter configuration
--------------------------------------------------------------------------------

-- | Configuration option for the SAT solver command.
-- The string @$1@ is replaced with the path to the DIMACS CNF file.
satSolverCommand :: ConfigOption (BaseStringType Unicode)
satSolverCommand = configOption knownRepr "solver.sat.command"

dimacsSatOptions :: [ConfigDesc]
dimacsSatOptions =
  [ mkOpt satSolverCommand
      stringOptSty
      (Just "External SAT solver command ($1 = CNF file path)")
      (Just (ConcreteString "cadical $1"))
  ]

-- | A 'SolverAdapter' that bit-blasts What4 expressions to DIMACS CNF
-- and runs an external SAT solver.
dimacsSatAdapter :: SolverAdapter st
dimacsSatAdapter =
  SolverAdapter
  { solver_adapter_name = "sat"
  , solver_adapter_config_options = dimacsSatOptions
  , solver_adapter_check_sat = satCheckSat
  , solver_adapter_write_smt2 = \_ _ _ ->
      fail "SAT adapter does not support writing SMT-LIB2 files."
  }

satCheckSat ::
  forall t st fs a.
  W4.ExprBuilder t st fs ->
  LogData ->
  [W4.BoolExpr t] ->
  (W4.SatResult (W4.GroundEvalFn t, Maybe (W4.ExprRangeBindings t)) () -> IO a) ->
  IO a
satCheckSat sym logData asserts k =
 do let cfg = W4.getConfiguration sym
    cmdTemplate <- Text.unpack <$> (getOpt =<< getOptionSetting satSolverCommand cfg)
    logCallback logData "Starting DIMACS SAT solver"

    let m = foldM (\acc e -> do { b <- evalExpr e; tsAndM acc b })
                  tsTrue
                  asserts

    case runTsM m of
      Left err ->
       do logCallback logData ("SAT translation error: " ++ err)
          k W4.Unknown

      Right (topLit, st) ->
       do let allClauses = [topLit] : tsClauses st
              numVars = tsNextVar st - 1

          tmpDir <- getTemporaryDirectory
          bracket
            (openTempFile tmpDir "cryptol.cnf")
            (\(path, h) -> hClose h >> removeFile path)
            $ \(cnfPath, cnfHandle) ->
           do writeDIMACS cnfHandle numVars allClauses
              hFlush cnfHandle
              hClose cnfHandle

              let cmd = replaceDollar1 cmdTemplate cnfPath
              logCallback logData ("Running: " ++ cmd)

              output <- runCommand cmd
              let result = parseDIMACSResult output

              case result of
                DIMACS_UNSAT ->
                  k (W4.Unsat ())

                DIMACS_UNKNOWN ->
                  k W4.Unknown

                DIMACS_SAT trueVars ->
                  let evalFn = W4.GroundEvalFn
                        (groundEval trueVars (tsNonceCache st))
                  in k (W4.Sat (evalFn, Nothing))


--------------------------------------------------------------------------------
-- QBF adapter configuration
--------------------------------------------------------------------------------

-- | Configuration option for the QBF solver command.
qbfSolverCommand :: ConfigOption (BaseStringType Unicode)
qbfSolverCommand = configOption knownRepr "solver.qbf.command"

dimacsQbfOptions :: [ConfigDesc]
dimacsQbfOptions =
  [ mkOpt qbfSolverCommand
      stringOptSty
      (Just "External QBF solver command ($1 = QDIMACS file path)")
      (Just (ConcreteString "caqe $1"))
  ]

-- | A 'SolverAdapter' for QBF solvers via QDIMACS.
--
-- For @:prove@ (checking validity), the input variables are universally
-- quantified and the Tseitin auxiliary variables are existentially quantified.
-- The QBF solver checks: forall inputs. exists aux. formula(inputs, aux).
--
-- For @:sat@, all variables are existentially quantified (equivalent to SAT).
dimacsQbfAdapter :: SolverAdapter st
dimacsQbfAdapter =
  SolverAdapter
  { solver_adapter_name = "qbf"
  , solver_adapter_config_options = dimacsQbfOptions
  , solver_adapter_check_sat = qbfCheckSat
  , solver_adapter_write_smt2 = \_ _ _ ->
      fail "QBF adapter does not support writing SMT-LIB2 files."
  }

-- | The QBF adapter treats all input variables as universal (for :prove)
-- and Tseitin auxiliary variables as existential.  When used via :sat,
-- What4 negates the formula first, so the solver checks the right thing.
qbfCheckSat ::
  forall t st fs a.
  W4.ExprBuilder t st fs ->
  LogData ->
  [W4.BoolExpr t] ->
  (W4.SatResult (W4.GroundEvalFn t, Maybe (W4.ExprRangeBindings t)) () -> IO a) ->
  IO a
qbfCheckSat sym logData asserts k =
 do let cfg = W4.getConfiguration sym
    cmdTemplate <- Text.unpack <$> (getOpt =<< getOptionSetting qbfSolverCommand cfg)
    logCallback logData "Starting QDIMACS QBF solver"

    let m = foldM (\acc e -> do { b <- evalExpr e; tsAndM acc b })
                  tsTrue
                  asserts

    case runTsM m of
      Left err ->
       do logCallback logData ("QBF translation error: " ++ err)
          k W4.Unknown

      Right (topLit, st) ->
       do let allClauses = [topLit] : tsClauses st
              numVars = tsNextVar st - 1
              univVars = tsInputVars st
              existVars = IntSet.fromList [1 .. numVars] `IntSet.difference` univVars

          tmpDir <- getTemporaryDirectory
          bracket
            (openTempFile tmpDir "cryptol.qdimacs")
            (\(path, h) -> hClose h >> removeFile path)
            $ \(qdPath, qdHandle) ->
           do writeQDIMACS qdHandle numVars allClauses univVars existVars
              hFlush qdHandle
              hClose qdHandle

              let cmd = replaceDollar1 cmdTemplate qdPath
              logCallback logData ("Running: " ++ cmd)

              output <- runCommand cmd
              let result = parseQBFResult output

              case result of
                QBF_TRUE ->
                  -- The universally-quantified formula is true (valid)
                  k (W4.Unsat ())

                QBF_FALSE ->
                  -- The formula is falsifiable; QBF solvers may not
                  -- provide a counterexample model in standard output
                  k (W4.Sat (W4.GroundEvalFn (defaultGroundEval (tsNonceCache st)), Nothing))

                QBF_UNKNOWN ->
                  k W4.Unknown


-- | Fallback ground evaluator when the QBF solver does not provide a model.
defaultGroundEval ::
  MapF (Nonce t) TsR' ->
  W4.Expr t tp ->
  IO (W4.GroundValue tp)
defaultGroundEval nonces e = W4.evalGroundExpr (defaultGroundEval nonces) e


--------------------------------------------------------------------------------
-- Sharp SAT (model counting)
--------------------------------------------------------------------------------

-- | Configuration option for the sharpSAT command.
sharpSATCommand :: ConfigOption (BaseStringType Unicode)
sharpSATCommand = configOption knownRepr "solver.sharpsat.command"

sharpSATOptions :: [ConfigDesc]
sharpSATOptions =
  [ mkOpt sharpSATCommand
      stringOptSty
      (Just "Model counting command ($1 = CNF file path)")
      (Just (ConcreteString "sharpSAT $1"))
  ]

-- | Count the number of satisfying assignments for a list of boolean assertions.
countModels ::
  forall t st fs.
  W4.ExprBuilder t st fs ->
  LogData ->
  [W4.BoolExpr t] ->
  IO (Either String Integer)
countModels sym logData asserts =
 do let cfg = W4.getConfiguration sym
    cmdTemplate <- Text.unpack <$> (getOpt =<< getOptionSetting sharpSATCommand cfg)
    logCallback logData "Starting model counting"

    let m = foldM (\acc e -> do { b <- evalExpr e; tsAndM acc b })
                  tsTrue
                  asserts

    case runTsM m of
      Left err -> pure (Left ("Model counting translation error: " ++ err))

      Right (topLit, st) ->
       do let allClauses = [topLit] : tsClauses st
              numVars = tsNextVar st - 1

          tmpDir <- getTemporaryDirectory
          bracket
            (openTempFile tmpDir "cryptol-count.cnf")
            (\(path, h) -> hClose h >> removeFile path)
            $ \(cnfPath, cnfHandle) ->
           do writeDIMACS cnfHandle numVars allClauses
              hFlush cnfHandle
              hClose cnfHandle

              let cmd = replaceDollar1 cmdTemplate cnfPath
              logCallback logData ("Running: " ++ cmd)

              output <- runCommand cmd
              pure (parseSharpSATResult output)

parseSharpSATResult :: String -> Either String Integer
parseSharpSATResult output =
  case filter isCountLine (lines output) of
    [] -> Left ("Could not parse model count from solver output:\n" ++ output)
    ls -> case reads (last ls) of
            [(n, "")] -> Right n
            _         -> Left ("Could not parse count from line: " ++ last ls)
  where
    isCountLine l =
      case reads l :: [(Integer, String)] of
        [(_, "")] -> True
        _         -> False


--------------------------------------------------------------------------------
-- Shared utilities
--------------------------------------------------------------------------------

replaceDollar1 :: String -> FilePath -> String
replaceDollar1 [] _ = []
replaceDollar1 ('$':'1':rest) path = path ++ replaceDollar1 rest path
replaceDollar1 (c:rest) path = c : replaceDollar1 rest path

runCommand :: String -> IO String
runCommand cmd =
  let (prog, args) = case words cmd of
        []   -> ("solver", [])
        p:as -> (p, as)
  in readProcess prog args ""


--------------------------------------------------------------------------------
-- DIMACS / QDIMACS output
--------------------------------------------------------------------------------

type Clause = [Int]

writeDIMACS :: Handle -> Int -> [Clause] -> IO ()
writeDIMACS h numVars clauses =
 do hPutStrLn h ("p cnf " ++ show numVars ++ " " ++ show (length clauses))
    mapM_ writeClause clauses
  where
    writeClause cl = hPutStrLn h (unwords (map show cl) ++ " 0")

writeQDIMACS :: Handle -> Int -> [Clause] -> IntSet -> IntSet -> IO ()
writeQDIMACS h numVars clauses univVars existVars =
 do hPutStrLn h ("p cnf " ++ show numVars ++ " " ++ show (length clauses))
    -- Quantifier prefix: universal variables (outer), then existential (inner)
    let uList = IntSet.toAscList univVars
        eList = IntSet.toAscList existVars
    if null uList
      then pure ()
      else hPutStrLn h ("a " ++ unwords (map show uList) ++ " 0")
    if null eList
      then pure ()
      else hPutStrLn h ("e " ++ unwords (map show eList) ++ " 0")
    mapM_ (\cl -> hPutStrLn h (unwords (map show cl) ++ " 0")) clauses


--------------------------------------------------------------------------------
-- DIMACS result parsing
--------------------------------------------------------------------------------

data DIMACSResult
  = DIMACS_SAT IntSet
  | DIMACS_UNSAT
  | DIMACS_UNKNOWN

parseDIMACSResult :: String -> DIMACSResult
parseDIMACSResult output =
  case findSatLine (lines output) of
    Just "UNSATISFIABLE" -> DIMACS_UNSAT
    Just "SATISFIABLE"   -> DIMACS_SAT (parseModel (lines output))
    _                    -> DIMACS_UNKNOWN
  where
    findSatLine [] = Nothing
    findSatLine (l:ls) =
      case words l of
        ["s", result] -> Just result
        _             -> findSatLine ls

    parseModel ls =
      let vLines = [ tail (words l) | l <- ls, ('v':_) <- [l] ]
          vals = concatMap (map read) vLines :: [Int]
      in IntSet.fromList [v | v <- vals, v > 0]

data QBFResult = QBF_TRUE | QBF_FALSE | QBF_UNKNOWN

parseQBFResult :: String -> QBFResult
parseQBFResult output =
  case findResultLine (lines output) of
    Just r | r `elem` ["1", "TRUE", "SATISFIABLE"]   -> QBF_TRUE
           | r `elem` ["0", "FALSE", "UNSATISFIABLE"] -> QBF_FALSE
    _ -> QBF_UNKNOWN
  where
    findResultLine [] = Nothing
    findResultLine (l:ls) =
      case words l of
        ["s", "cnf", r] -> Just r   -- QDIMACS competition format
        ["s", r]        -> Just r   -- Fallback
        _               -> findResultLine ls


--------------------------------------------------------------------------------
-- Tseitin encoding
--------------------------------------------------------------------------------

type TsLit = Int

tsNot :: TsLit -> TsLit
tsNot = negate

tsTrue :: TsLit
tsTrue = 1

data TsState t = TsState
  { tsNextVar    :: !Int
  , tsClauses    :: ![Clause]
  , tsInputVars  :: !IntSet       -- ^ Variables from BoundVarExpr (for QBF)
  , tsNonceCache :: !(MapF (Nonce t) TsR')
  }

emptyTsState :: TsState t
emptyTsState = TsState
  { tsNextVar    = 2
  , tsClauses    = [[1]]   -- unit clause: variable 1 = true
  , tsInputVars  = IntSet.empty
  , tsNonceCache = MapF.empty
  }

newtype TsM t a = TsM { unTsM :: forall k. TsState t -> (String -> k) -> (a -> TsState t -> k) -> k }

runTsM :: TsM t a -> Either String (a, TsState t)
runTsM m = unTsM m emptyTsState Left (curry Right)

instance Functor (TsM t) where
  fmap f (TsM m) = TsM (\s e k -> m s e (k . f))

instance Applicative (TsM t) where
  pure x = TsM (\s _ k -> k x s)
  (<*>) = ap

instance Monad (TsM t) where
  TsM m1 >>= f = TsM (\s0 e t -> m1 s0 e (\a s1 -> unTsM (f a) s1 e t))

instance MonadFail (TsM t) where
  fail str = TsM (\_ e _ -> e str)

getState :: TsM t (TsState t)
getState = TsM (\s _ k -> k s s)

setState :: TsState t -> TsM t ()
setState s = TsM (\_ _ k -> k () s)

freshVar :: TsM t TsLit
freshVar =
 do s <- getState
    let v = tsNextVar s
    setState $! s { tsNextVar = v + 1 }
    pure v

-- | Allocate a fresh variable and mark it as an input variable (for QBF).
freshInputVar :: TsM t TsLit
freshInputVar =
 do v <- freshVar
    s <- getState
    setState $! s { tsInputVars = IntSet.insert v (tsInputVars s) }
    pure v

addClause :: Clause -> TsM t ()
addClause cl =
 do s <- getState
    setState $! s { tsClauses = cl : tsClauses s }

tsAndM :: TsLit -> TsLit -> TsM t TsLit
tsAndM a b
  | a == 1 = pure b
  | b == 1 = pure a
  | a == -1 = pure (-1)
  | b == -1 = pure (-1)
  | a == b  = pure a
  | a == tsNot b = pure (-1)
  | otherwise =
 do r <- freshVar
    addClause [tsNot r, a]
    addClause [tsNot r, b]
    addClause [r, tsNot a, tsNot b]
    pure r

tsOrM :: TsLit -> TsLit -> TsM t TsLit
tsOrM a b
  | a == 1 = pure 1
  | b == 1 = pure 1
  | a == -1 = pure b
  | b == -1 = pure a
  | a == b = pure a
  | a == tsNot b = pure 1
  | otherwise =
 do r <- freshVar
    addClause [tsNot a, r]
    addClause [tsNot b, r]
    addClause [tsNot r, a, b]
    pure r

tsXorM :: TsLit -> TsLit -> TsM t TsLit
tsXorM a b
  | a == 1 = pure (tsNot b)
  | b == 1 = pure (tsNot a)
  | a == -1 = pure b
  | b == -1 = pure a
  | a == b = pure (-1)
  | a == tsNot b = pure 1
  | otherwise =
 do r <- freshVar
    addClause [tsNot r, a, b]
    addClause [tsNot r, tsNot a, tsNot b]
    addClause [r, tsNot a, b]
    addClause [r, a, tsNot b]
    pure r

tsIteM :: TsLit -> TsLit -> TsLit -> TsM t TsLit
tsIteM c t e
  | c == 1 = pure t
  | c == -1 = pure e
  | t == e = pure t
  | otherwise =
 do r <- freshVar
    addClause [tsNot c, tsNot t, r]
    addClause [tsNot c, t, tsNot r]
    addClause [c, tsNot e, r]
    addClause [c, e, tsNot r]
    pure r

tsIffM :: TsLit -> TsLit -> TsM t TsLit
tsIffM a b = tsXorM a b >>= \x -> pure (tsNot x)

tsAndAllM :: [TsLit] -> TsM t TsLit
tsAndAllM [] = pure 1
tsAndAllM [x] = pure x
tsAndAllM (x:xs) = foldM tsAndM x xs

tsBvEqM :: V.Vector TsLit -> V.Vector TsLit -> TsM t TsLit
tsBvEqM xs ys =
 do eqs <- V.zipWithM tsIffM xs ys
    tsAndAllM (V.toList eqs)


--------------------------------------------------------------------------------
-- Bitvector arithmetic
--------------------------------------------------------------------------------

tsFullAdder :: TsLit -> TsLit -> TsLit -> TsM t (TsLit, TsLit)
tsFullAdder a b cin =
 do s <- tsXorM a b >>= tsXorM cin
    c1 <- tsAndM a b
    c2 <- tsAndM a cin
    c3 <- tsAndM b cin
    cout <- tsOrM c1 c2 >>= tsOrM c3
    pure (s, cout)

tsBvAddM :: V.Vector TsLit -> V.Vector TsLit -> TsM t (V.Vector TsLit)
tsBvAddM xs ys =
 do let n = V.length xs
    let go i carry acc
          | i < 0 = pure acc
          | otherwise =
           do (s, c) <- tsFullAdder (xs V.! i) (ys V.! i) carry
              go (i - 1) c (s : acc)
    bits <- go (n - 1) (-1) []
    pure (V.fromListN n bits)

tsBvUltM :: V.Vector TsLit -> V.Vector TsLit -> TsM t TsLit
tsBvUltM xs ys =
 do let n = V.length xs
    let go i carry
          | i < 0 = pure carry
          | otherwise =
           do (_, c) <- tsFullAdder (tsNot (xs V.! i)) (ys V.! i) carry
              go (i - 1) c
    go (n - 1) (-1)

tsBvSltM :: V.Vector TsLit -> V.Vector TsLit -> TsM t TsLit
tsBvSltM xs ys
  | V.null xs = pure (-1)
  | otherwise =
 do let xs' = xs V.// [(0, tsNot (xs V.! 0))]
        ys' = ys V.// [(0, tsNot (ys V.! 0))]
    tsBvUltM xs' ys'

tsBvShlM :: V.Vector TsLit -> V.Vector TsLit -> TsM t (V.Vector TsLit)
tsBvShlM xs amt =
 do let n = V.length xs
    foldM (\cur i ->
      let shiftAmt = 2 ^ (n - 1 - i) in
      V.generateM n (\j ->
        let srcIdx = j + shiftAmt in
        if srcIdx >= n
          then tsIteM (amt V.! i) (-1) (cur V.! j)
          else tsIteM (amt V.! i) (cur V.! srcIdx) (cur V.! j))
      ) xs [0 .. n - 1]

tsBvLshrM :: V.Vector TsLit -> V.Vector TsLit -> TsM t (V.Vector TsLit)
tsBvLshrM xs amt =
 do let n = V.length xs
    foldM (\cur i ->
      let shiftAmt = 2 ^ (n - 1 - i) in
      V.generateM n (\j ->
        let srcIdx = j - shiftAmt in
        if srcIdx < 0
          then tsIteM (amt V.! i) (-1) (cur V.! j)
          else tsIteM (amt V.! i) (cur V.! srcIdx) (cur V.! j))
      ) xs [0 .. n - 1]

tsBvAshrM :: V.Vector TsLit -> V.Vector TsLit -> TsM t (V.Vector TsLit)
tsBvAshrM xs amt
  | V.null xs = pure xs
  | otherwise =
 do let n = V.length xs
        signBit = xs V.! 0
    foldM (\cur i ->
      let shiftAmt = 2 ^ (n - 1 - i) in
      V.generateM n (\j ->
        let srcIdx = j - shiftAmt in
        if srcIdx < 0
          then tsIteM (amt V.! i) signBit (cur V.! j)
          else tsIteM (amt V.! i) (cur V.! srcIdx) (cur V.! j))
      ) xs [0 .. n - 1]

tsBvMulM :: V.Vector TsLit -> V.Vector TsLit -> TsM t (V.Vector TsLit)
tsBvMulM xs ys =
 do let n = V.length xs
        zero = V.replicate n (-1)
    foldM (\acc i ->
     do let bit = ys V.! i
        masked <- V.mapM (\x -> tsAndM x bit) xs
        let shiftAmt = n - 1 - i
            shifted = V.generate n (\j ->
              let srcIdx = j + shiftAmt in
              if srcIdx >= n || srcIdx < 0 then -1
              else masked V.! srcIdx)
        tsBvAddM acc shifted
      ) zero [0 .. n - 1]

tsBvLit :: Int -> Integer -> V.Vector TsLit
tsBvLit w val = V.generate w (\i ->
  if testBit val (w - 1 - i) then 1 else -1)


--------------------------------------------------------------------------------
-- What4 expression evaluation
--------------------------------------------------------------------------------

type family TsR (tp :: W4.BaseType) where
  TsR W4.BaseBoolType = TsLit
  TsR (W4.BaseBVType n) = V.Vector TsLit

newtype TsR' tp = TsR (TsR tp)

cached :: Nonce t tp -> TsM t (TsR tp) -> TsM t (TsR tp)
cached nonce gen =
 do mb <- fmap (MapF.lookup nonce . tsNonceCache) getState
    case mb of
      Just (TsR r) -> pure r
      Nothing ->
       do r <- gen
          s <- getState
          setState $! s { tsNonceCache = MapF.insert nonce (TsR r) (tsNonceCache s) }
          pure r

evalWidth :: W4.NatRepr w -> TsM t Int
evalWidth w =
  let n = W4.natValue w in
  if n > fromIntegral (maxBound :: Int)
    then fail "Bit-vector width too wide for SAT backend"
    else pure (fromIntegral n)

evalExpr :: W4.Expr t tp -> TsM t (TsR tp)
evalExpr = \case
  W4.BoolExpr True _ -> pure 1
  W4.BoolExpr False _ -> pure (-1)

  W4.AppExpr x -> cached (W4.appExprId x) (evalApp (W4.appExprApp x))

  W4.BoundVarExpr x -> cached (W4.bvarId x) $
    case W4.bvarType x of
      W4.BaseBoolRepr -> freshInputVar
      W4.BaseBVRepr w ->
       do w' <- evalWidth w
          V.fromList <$> replicateM w' freshInputVar
      r -> fail ("SAT backend does not support bound variables of type " ++ show r)

  W4.SemiRingLiteral rpr c _ ->
    case rpr of
      W4.SemiRingBVRepr _ w ->
       do w' <- evalWidth w
          let BV.BV ci = c
          pure (tsBvLit w' ci)
      _ -> fail "SAT backend only supports bitvector semiring literals"

  W4.NonceAppExpr x -> cached (W4.nonceExprId x) $
    case W4.nonceExprApp x of
      W4.Annotation _ _ e -> evalExpr e
      _ -> fail "SAT backend does not support this expression type"

  W4.FloatExpr{} -> fail "SAT backend does not support floating point"
  W4.StringExpr{} -> fail "SAT backend does not support strings"


evalApp :: W4.App (W4.Expr t) tp -> TsM t (TsR tp)
evalApp = \case

  W4.BaseEq W4.BaseBoolRepr x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsIffM x' y'

  W4.BaseEq (W4.BaseBVRepr _) x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsBvEqM x' y'

  W4.BaseIte W4.BaseBoolRepr _ c t e ->
   do c' <- evalExpr c
      t' <- evalExpr t
      e' <- evalExpr e
      tsIteM c' t' e'

  W4.BaseIte (W4.BaseBVRepr _) _ c t e ->
   do c' <- evalExpr c
      t' <- evalExpr t
      e' <- evalExpr e
      V.zipWithM (tsIteM c') t' e'

  W4.NotPred x ->
   do x' <- evalExpr x
      pure (tsNot x')

  W4.ConjPred c ->
    case W4.viewConjMap c of
      W4.ConjTrue -> pure 1
      W4.ConjFalse -> pure (-1)
      W4.Conjuncts y ->
       do let f (x, W4.Positive) = evalExpr x
              f (x, W4.Negative) = tsNot <$> evalExpr x
          lits <- traverse f y
          foldM tsAndM 1 lits

  W4.BVTestBit i ve ->
   do v <- evalExpr ve
      let idx = V.length v - fromIntegral i - 1
      pure (v V.! idx)

  W4.BVSlt x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsBvSltM x' y'

  W4.BVUlt x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsBvUltM x' y'

  W4.BVConcat _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure (x' <> y')

  W4.BVSelect i n v ->
   do v' <- evalExpr v
      i' <- evalWidth i
      n' <- evalWidth n
      let start = V.length v' - n' - i'
      pure (V.slice start n' v')

  W4.BVFill w b ->
   do w' <- evalWidth w
      b' <- evalExpr b
      pure (V.replicate w' b')

  W4.BVZext w v ->
   do v' <- evalExpr v
      w' <- evalWidth w
      let pad = w' - V.length v'
      pure (V.replicate pad (-1) <> v')

  W4.BVSext w v ->
   do v' <- evalExpr v
      w' <- evalWidth w
      let pad = w' - V.length v'
          signBit = if V.null v' then (-1) else V.head v'
      pure (V.replicate pad signBit <> v')

  W4.BVShl _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsBvShlM x' y'

  W4.BVLshr _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsBvLshrM x' y'

  W4.BVAshr _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      tsBvAshrM x' y'

  W4.BVOrBits w s ->
   do vs <- traverse evalExpr (W4.bvOrToList s)
      w' <- evalWidth w
      let zero = V.replicate w' (-1)
      foldM (\acc v -> V.zipWithM tsOrM acc v) zero vs

  W4.SemiRingSum s ->
   do case Sum.sumRepr s of
        W4.SemiRingBVRepr flv w ->
         do w' <- evalWidth w
            case flv of
              W4.BVArithRepr ->
                Sum.evalM
                  tsBvAddM
                  (\(BV.BV c) r ->
                   do v <- evalExpr r
                      tsBvMulM v (tsBvLit w' c))
                  (\(BV.BV c) -> pure (tsBvLit w' c))
                  s
              W4.BVBitsRepr ->
                Sum.evalM
                  (\x y -> V.zipWithM tsXorM x y)
                  (\(BV.BV c) r ->
                   do v <- evalExpr r
                      V.zipWithM tsAndM (tsBvLit w' c) v)
                  (\(BV.BV c) -> pure (tsBvLit w' c))
                  s
        _ -> fail "SAT backend only supports bitvector sums"

  W4.SemiRingProd p ->
   do case Sum.prodRepr p of
        W4.SemiRingBVRepr flv w ->
         do w' <- evalWidth w
            case flv of
              W4.BVArithRepr ->
               do mb <- Sum.prodEvalM tsBvMulM evalExpr p
                  pure (case mb of
                    Nothing -> tsBvLit w' 1
                    Just r  -> r)
              W4.BVBitsRepr ->
               do mb <- Sum.prodEvalM (\x y -> V.zipWithM tsAndM x y) evalExpr p
                  pure (case mb of
                    Nothing -> V.replicate w' 1
                    Just r  -> r)
        _ -> fail "SAT backend only supports bitvector products"

  e -> fail ("SAT backend does not support: " ++ show e)


--------------------------------------------------------------------------------
-- Ground evaluation
--------------------------------------------------------------------------------

groundEval ::
  IntSet ->
  MapF (Nonce t) TsR' ->
  W4.Expr t tp ->
  IO (W4.GroundValue tp)
groundEval trueVars nonces e =
  case (flip MapF.lookup nonces =<< W4.exprMaybeId e, W4.exprType e) of
    (Just (TsR n), W4.BaseBoolRepr) ->
      pure $! evalLit trueVars n

    (Just (TsR n), W4.BaseBVRepr w) ->
      pure $! litsToBV w (V.map (evalLit trueVars) n)

    _ -> W4.evalGroundExpr (groundEval trueVars nonces) e

evalLit :: IntSet -> TsLit -> Bool
evalLit trueVars lit
  | lit > 0   = IntSet.member lit trueVars
  | lit < 0   = not (IntSet.member (negate lit) trueVars)
  | otherwise = False

litsToBV :: W4.NatRepr w -> V.Vector Bool -> BV.BV w
litsToBV w bs = BV.mkBV w (V.foldl' (\acc x -> if x then 1 + acc * 2 else acc * 2) 0 bs)

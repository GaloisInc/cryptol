-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Prover
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Provable abstraction and the connection to SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE BangPatterns         #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate, Provable(..)
       , ThmResult(..), SatResult(..), AllSatResult(..), SMTResult(..)
       , isSatisfiable, isSatisfiableWith, isTheorem, isTheoremWith
       , prove, proveWith
       , sat, satWith
       , allSat, allSatWith
       , isVacuous, isVacuousWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , boolector, cvc4, yices, z3, mathSAT, defaultSMTCfg
       , compileToSMTLib, generateSMTBenchmarks
       , isSBranchFeasibleInState
       ) where

import Control.Monad       (when, unless)
import Control.Monad.Trans (liftIO)
import Data.List           (intercalate)
import Data.Maybe          (mapMaybe, fromMaybe)
import System.FilePath     (addExtension, splitExtension)
import System.Time         (getClockTime)
import System.IO.Unsafe    (unsafeInterleaveIO)

import qualified Data.Set as Set (Set, toList)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import qualified Data.SBV.Provers.Boolector  as Boolector
import qualified Data.SBV.Provers.CVC4       as CVC4
import qualified Data.SBV.Provers.Yices      as Yices
import qualified Data.SBV.Provers.Z3         as Z3
import qualified Data.SBV.Provers.MathSAT    as MathSAT
import Data.SBV.Utils.TDiff

mkConfig :: SMTSolver -> Bool -> [String] -> SMTConfig
mkConfig s isSMTLib2 tweaks = SMTConfig { verbose        = False
                                        , timing         = False
                                        , sBranchTimeOut = Nothing
                                        , timeOut        = Nothing
                                        , printBase      = 10
                                        , printRealPrec  = 16
                                        , smtFile        = Nothing
                                        , solver         = s
                                        , solverTweaks   = tweaks
                                        , useSMTLib2     = isSMTLib2
                                        , satCmd         = "(check-sat)"
                                        , roundingMode   = RoundNearestTiesToEven
                                        , useLogic       = Nothing
                                        }

-- | Default configuration for the Boolector SMT solver
boolector :: SMTConfig
boolector = mkConfig Boolector.boolector True []

-- | Default configuration for the CVC4 SMT Solver.
cvc4 :: SMTConfig
cvc4 = mkConfig CVC4.cvc4 True []

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = mkConfig Yices.yices False []

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = mkConfig Z3.z3 True ["(set-option :smt.mbqi true) ; use model based quantifier instantiation"]

-- | Default configuration for the MathSAT SMT solver
mathSAT :: SMTConfig
mathSAT = mkConfig MathSAT.mathSAT True []

-- | The default solver used by SBV. This is currently set to z3.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = z3

-- | A predicate is a symbolic program that returns a (symbolic) boolean value. For all intents and
-- purposes, it can be treated as an n-ary function from symbolic-values to a boolean. The 'Symbolic'
-- monad captures the underlying representation, and can/should be ignored by the users of the library,
-- unless you are building further utilities on top of SBV itself. Instead, simply use the 'Predicate'
-- type when necessary.
type Predicate = Symbolic SBool

-- | A type @a@ is provable if we can turn it into a predicate.
-- Note that a predicate can be made from a curried function of arbitrary arity, where
-- each element is either a symbolic type or up-to a 7-tuple of symbolic-types. So
-- predicates can be constructed from almost arbitrary Haskell functions that have arbitrary
-- shapes. (See the instance declarations below.)
class Provable a where
  -- | Turns a value into a universally quantified predicate, internally naming the inputs.
  -- In this case the sbv library will use names of the form @s1, s2@, etc. to name these variables
  -- Example:
  --
  -- >  forAll_ $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- is a predicate with two arguments, captured using an ordinary Haskell function. Internally,
  -- @x@ will be named @s0@ and @y@ will be named @s1@.
  forAll_ :: a -> Predicate
  -- | Turns a value into a predicate, allowing users to provide names for the inputs.
  -- If the user does not provide enough number of names for the variables, the remaining ones
  -- will be internally generated. Note that the names are only used for printing models and has no
  -- other significance; in particular, we do not check that they are unique. Example:
  --
  -- >  forAll ["x", "y"] $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- This is the same as above, except the variables will be named @x@ and @y@ respectively,
  -- simplifying the counter-examples when they are printed.
  forAll  :: [String] -> a -> Predicate
  -- | Turns a value into an existentially quantified predicate. (Indeed, 'exists' would have been
  -- a better choice here for the name, but alas it's already taken.)
  forSome_ :: a -> Predicate
  -- | Version of 'forSome' that allows user defined names
  forSome :: [String] -> a -> Predicate

instance Provable Predicate where
  forAll_    = id
  forAll []  = id
  forAll xs  = error $ "SBV.forAll: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs
  forSome_   = id
  forSome [] = id
  forSome xs = error $ "SBV.forSome: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs

instance Provable SBool where
  forAll_   = return
  forAll _  = return
  forSome_  = return
  forSome _ = return

{-
-- The following works, but it lets us write properties that
-- are not useful.. Such as: prove $ \x y -> (x::SInt8) == y
-- Running that will throw an exception since Haskell's equality
-- is not be supported by symbolic things. (Needs .==).
instance Provable Bool where
  forAll_  x  = forAll_   (if x then true else false :: SBool)
  forAll s x  = forAll s  (if x then true else false :: SBool)
  forSome_  x = forSome_  (if x then true else false :: SBool)
  forSome s x = forSome s (if x then true else false :: SBool)
-}

-- Functions
instance (SymWord a, Provable p) => Provable (SBV a -> p) where
  forAll_        k = forall_   >>= \a -> forAll_   $ k a
  forAll (s:ss)  k = forall s  >>= \a -> forAll ss $ k a
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ k a
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ k a
  forSome []     k = forSome_ k

-- Arrays (memory), only supported universally for the time being
instance (HasKind a, HasKind b, SymArray array, Provable p) => Provable (array a b -> p) where
  forAll_       k = newArray_  Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = newArray s Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome: Existential arrays are not currently supported."

-- 2 Tuple
instance (SymWord a, SymWord b, Provable p) => Provable ((SBV a, SBV b) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b -> k (a, b)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b -> k (a, b)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b -> k (a, b)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b -> k (a, b)
  forSome []     k = forSome_ k

-- 3 Tuple
instance (SymWord a, SymWord b, SymWord c, Provable p) => Provable ((SBV a, SBV b, SBV c) -> p) where
  forAll_       k  = forall_  >>= \a -> forAll_   $ \b c -> k (a, b, c)
  forAll (s:ss) k  = forall s >>= \a -> forAll ss $ \b c -> k (a, b, c)
  forAll []     k  = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c -> k (a, b, c)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c -> k (a, b, c)
  forSome []     k = forSome_ k

-- 4 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d -> k (a, b, c, d)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d -> k (a, b, c, d)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d -> k (a, b, c, d)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d -> k (a, b, c, d)
  forSome []     k = forSome_ k

-- 5 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e -> k (a, b, c, d, e)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e -> k (a, b, c, d, e)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e -> k (a, b, c, d, e)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e -> k (a, b, c, d, e)
  forSome []     k = forSome_ k

-- 6 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f -> k (a, b, c, d, e, f)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f -> k (a, b, c, d, e, f)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f -> k (a, b, c, d, e, f)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f -> k (a, b, c, d, e, f)
  forSome []     k = forSome_ k

-- 7 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome []     k = forSome_ k

-- | Prove a predicate, equivalent to @'proveWith' 'defaultSMTCfg'@
prove :: Provable a => a -> IO ThmResult
prove = proveWith defaultSMTCfg

-- | Find a satisfying assignment for a predicate, equivalent to @'satWith' 'defaultSMTCfg'@
sat :: Provable a => a -> IO SatResult
sat = satWith defaultSMTCfg

-- | Return all satisfying assignments for a predicate, equivalent to @'allSatWith' 'defaultSMTCfg'@.
-- Satisfying assignments are constructed lazily, so they will be available as returned by the solver
-- and on demand.
--
-- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
-- the purposes of @'allSat'@. That is, only the satisfying assignments modulo uninterpreted functions and
-- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
-- function counter-example back from the SMT solver.
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith defaultSMTCfg

-- | Check if the given constraints are satisfiable, equivalent to @'isVacuousWith' 'defaultSMTCfg'@.
-- See the function 'constrain' for an example use of 'isVacuous'.
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith defaultSMTCfg

-- Decision procedures (with optional timeout)

-- | Check whether a given property is a theorem, with an optional time out and the given solver.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheoremWith :: Provable a => SMTConfig -> Maybe Int -> a -> IO (Maybe Bool)
isTheoremWith cfg mbTo p = do r <- proveWith cfg{timeOut = mbTo} p
                              case r of
                                ThmResult (Unsatisfiable _) -> return $ Just True
                                ThmResult (Satisfiable _ _) -> return $ Just False
                                ThmResult (TimeOut _)       -> return Nothing
                                _                           -> error $ "SBV.isTheorem: Received:\n" ++ show r

-- | Check whether a given property is satisfiable, with an optional time out and the given solver.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiableWith :: Provable a => SMTConfig -> Maybe Int -> a -> IO (Maybe Bool)
isSatisfiableWith cfg mbTo p = do r <- satWith cfg{timeOut = mbTo} p
                                  case r of
                                    SatResult (Satisfiable _ _) -> return $ Just True
                                    SatResult (Unsatisfiable _) -> return $ Just False
                                    SatResult (TimeOut _)       -> return Nothing
                                    _                           -> error $ "SBV.isSatisfiable: Received: " ++ show r

-- | Checks theoremhood within the given optional time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isTheorem = isTheoremWith defaultSMTCfg

-- | Checks satisfiability within the given optional time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isSatisfiable = isSatisfiableWith defaultSMTCfg

-- | Compiles to SMT-Lib and returns the resulting program as a string. Useful for saving
-- the result to a file for off-line analysis, for instance if you have an SMT solver that's not natively
-- supported out-of-the box by the SBV library. It takes two booleans:
--
--    * smtLib2: If 'True', will generate SMT-Lib2 output, otherwise SMT-Lib1 output
--
--    * isSat  : If 'True', will translate it as a SAT query, i.e., in the positive. If 'False', will
--               translate as a PROVE query, i.e., it will negate the result. (In this case, the check-sat
--               call to the SMT solver will produce UNSAT if the input is a theorem, as usual.)
compileToSMTLib :: Provable a => Bool   -- ^ If True, output SMT-Lib2, otherwise SMT-Lib1
                              -> Bool   -- ^ If True, translate directly, otherwise negate the goal. (Use True for SAT queries, False for PROVE queries.)
                              -> a
                              -> IO String
compileToSMTLib smtLib2 isSat a = do
        t <- getClockTime
        let comments = ["Created on " ++ show t]
            cvt = if smtLib2 then toSMTLib2 else toSMTLib1
        (_, _, _, _, smtLibPgm) <- simulate cvt defaultSMTCfg isSat comments a
        let out = show smtLibPgm
        return $ out ++ if smtLib2 -- append check-sat in case of smtLib2
                        then "\n(check-sat)\n"
                        else "\n"

-- | Create both SMT-Lib1 and SMT-Lib2 benchmarks. The first argument is the basename of the file,
-- SMT-Lib1 version will be written with suffix ".smt1" and SMT-Lib2 version will be written with
-- suffix ".smt2". The 'Bool' argument controls whether this is a SAT instance, i.e., translate the query
-- directly, or a PROVE instance, i.e., translate the negated query. (See the second boolean argument to
-- 'compileToSMTLib' for details.)
generateSMTBenchmarks :: Provable a => Bool -> FilePath -> a -> IO ()
generateSMTBenchmarks isSat f a = gen False smt1 >> gen True smt2
  where smt1     = addExtension f "smt1"
        smt2     = addExtension f "smt2"
        gen b fn = do s <- compileToSMTLib b isSat a
                      writeFile fn s
                      putStrLn $ "Generated SMT benchmark " ++ show fn ++ "."

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith config a = simulate cvt config False [] a >>= callSolver False "Checking Theoremhood.." ThmResult config
  where cvt = if useSMTLib2 config then toSMTLib2 else toSMTLib1

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith config a = simulate cvt config True [] a >>= callSolver True "Checking Satisfiability.." SatResult config
  where cvt = if useSMTLib2 config then toSMTLib2 else toSMTLib1

-- | Determine if the constraints are vacuous using the given SMT-solver
isVacuousWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousWith config a = do
        Result ki tr uic is cs ts as uis ax asgn cstr _ <- runSymbolic (True, Just config) $ forAll_ a >>= output
        case cstr of
           [] -> return False -- no constraints, no need to check
           _  -> do let is'  = [(EX, i) | (_, i) <- is] -- map all quantifiers to "exists" for the constraint check
                        res' = Result ki tr uic is' cs ts as uis ax asgn cstr [trueSW]
                        cvt  = if useSMTLib2 config then toSMTLib2 else toSMTLib1
                    SatResult result <- runProofOn cvt config True [] res' >>= callSolver True "Checking Satisfiability.." SatResult config
                    case result of
                      Unsatisfiable{} -> return True  -- constraints are unsatisfiable!
                      Satisfiable{}   -> return False -- constraints are satisfiable!
                      Unknown{}       -> error "SBV: isVacuous: Solver returned unknown!"
                      ProofError _ ls -> error $ "SBV: isVacuous: error encountered:\n" ++ unlines ls
                      TimeOut _       -> error "SBV: isVacuous: time-out."

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith config p = do
        let converter = if useSMTLib2 config then toSMTLib2 else toSMTLib1
        msg "Checking Satisfiability, all solutions.."
        sbvPgm@(qinps, _, _, ki, _) <- simulate converter config True [] p
        let usorts = [s | KUninterpreted s <- Set.toList ki]
        unless (null usorts) $ msg $  "SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                   ++ "\n               SBV will use equivalence classes to generate all-satisfying instances."
        results <- unsafeInterleaveIO $ go sbvPgm (1::Int) []
        -- See if there are any existentials below any universals
        -- If such is the case, then the solutions are unique upto prefix existentials
        let w = ALL `elem` map fst qinps
        return $ AllSatResult (w,  results)
  where msg = when (verbose config) . putStrLn . ("** " ++)
        go sbvPgm = loop
          where loop !n nonEqConsts = do
                  curResult <- invoke nonEqConsts n sbvPgm
                  case curResult of
                    Nothing            -> return []
                    Just (SatResult r) -> let cont model = do rest <- unsafeInterleaveIO $ loop (n+1) (modelAssocs model : nonEqConsts)
                                                              return (r : rest)
                                          in case r of
                                               Satisfiable _ (SMTModel [] _ _) -> return [r]
                                               Unknown _ (SMTModel [] _ _)     -> return [r]
                                               ProofError _ _                  -> return [r]
                                               TimeOut _                       -> return []
                                               Unsatisfiable _                 -> return []
                                               Satisfiable _ model             -> cont model
                                               Unknown     _ model             -> cont model
        invoke nonEqConsts n (qinps, modelMap, skolemMap, _, smtLibPgm) = do
               msg $ "Looking for solution " ++ show n
               case addNonEqConstraints (roundingMode config) qinps nonEqConsts smtLibPgm of
                 Nothing ->  -- no new constraints added, stop
                            return Nothing
                 Just finalPgm -> do msg $ "Generated SMTLib program:\n" ++ finalPgm
                                     smtAnswer <- engine (solver config) (updateName (n-1) config) True qinps modelMap skolemMap finalPgm
                                     msg "Done.."
                                     return $ Just $ SatResult smtAnswer
        updateName i cfg = cfg{smtFile = upd `fmap` smtFile cfg}
               where upd nm = let (b, e) = splitExtension nm in b ++ "_allSat_" ++ show i ++ e

type SMTProblem = ( [(Quantifier, NamedSymVar)]         -- inputs
                  , [(String, UnintKind)]               -- model-map
                  , [Either SW (SW, [SW])]              -- skolem-map
                  , Set.Set Kind                        -- kinds used
                  , SMTLibPgm                           -- SMTLib representation
                  )

callSolver :: Bool -> String -> (SMTResult -> b) -> SMTConfig -> SMTProblem -> IO b
callSolver isSat checkMsg wrap config (qinps, modelMap, skolemMap, _, smtLibPgm) = do
       let msg = when (verbose config) . putStrLn . ("** " ++)
       msg checkMsg
       let finalPgm = intercalate "\n" (pre ++ post) where SMTLibPgm _ (_, pre, post) = smtLibPgm
       msg $ "Generated SMTLib program:\n" ++ finalPgm
       smtAnswer <- engine (solver config) config isSat qinps modelMap skolemMap finalPgm
       msg "Done.."
       return $ wrap smtAnswer

simulate :: Provable a => SMTLibConverter -> SMTConfig -> Bool -> [String] -> a -> IO SMTProblem
simulate converter config isSat comments predicate = do
        let msg = when (verbose config) . putStrLn . ("** " ++)
            isTiming = timing config
        msg "Starting symbolic simulation.."
        res <- timeIf isTiming "problem construction" $ runSymbolic (isSat, Just config) $ (if isSat then forSome_ else forAll_) predicate >>= output
        msg $ "Generated symbolic trace:\n" ++ show res
        msg "Translating to SMT-Lib.."
        runProofOn converter config isSat comments res

runProofOn :: SMTLibConverter -> SMTConfig -> Bool -> [String] -> Result -> IO SMTProblem
runProofOn converter config isSat comments res =
        let isTiming   = timing config
            solverCaps = capabilities (solver config)
        in case res of
             Result ki _qcInfo _codeSegs is consts tbls arrs uis axs pgm cstrs [o@(SW KBool _)] ->
               timeIf isTiming "translation"
                $ let uiMap     = mapMaybe arrayUIKind arrs ++ map unintFnUIKind uis
                      skolemMap = skolemize (if isSat then is else map flipQ is)
                           where flipQ (ALL, x) = (EX, x)
                                 flipQ (EX, x)  = (ALL, x)
                                 skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
                                 skolemize qinps = go qinps ([], [])
                                   where go []                   (_,  sofar) = reverse sofar
                                         go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                                         go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)
                  in return (is, uiMap, skolemMap, ki, converter (roundingMode config) (useLogic config) solverCaps ki isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o)
             Result _kindInfo _qcInfo _codeSegs _is _consts _tbls _arrs _uis _axs _pgm _cstrs os -> case length os of
                           0  -> error $ "Impossible happened, unexpected non-outputting result\n" ++ show res
                           1  -> error $ "Impossible happened, non-boolean output in " ++ show os
                                       ++ "\nDetected while generating the trace:\n" ++ show res
                           _  -> error $ "User error: Multiple output values detected: " ++ show os
                                       ++ "\nDetected while generating the trace:\n" ++ show res
                                       ++ "\n*** Check calls to \"output\", they are typically not needed!"

-- | Check if a branch condition is feasible in the current state
isSBranchFeasibleInState :: State -> String -> SBool -> IO Bool
isSBranchFeasibleInState st branch cond = do
       let cfg = let pickedConfig = fromMaybe defaultSMTCfg (getSBranchRunConfig st)
                 in pickedConfig { timeOut = sBranchTimeOut pickedConfig }
           msg = when (verbose cfg) . putStrLn . ("** " ++)
       sw <- sbvToSW st cond
       () <- forceSWArg sw
       Result ki tr uic is cs ts as uis ax asgn cstr _ <- liftIO $ extractSymbolicSimulationState st
       let -- Construct the corresponding sat-checker for the branch. Note that we need to
           -- forget about the quantifiers and just use an "exist", as we're looking for a
           -- point-satisfiability check here; whatever the original program was.
           pgm = Result ki tr uic [(EX, n) | (_, n) <- is] cs ts as uis ax asgn cstr [sw]
           cvt = if useSMTLib2 cfg then toSMTLib2 else toSMTLib1
       check <- runProofOn cvt cfg True [] pgm >>= callSolver True ("sBranch: Checking " ++ show branch ++ " feasibility") SatResult cfg
       res <- case check of
                SatResult (Unsatisfiable _) -> return False
                _                           -> return True   -- No risks, even if it timed-our or anything else, we say it's feasible
       msg $ "sBranch: Conclusion: " ++ if res then "Feasible" else "Unfeasible"
       return res

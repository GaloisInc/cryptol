---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- (The sbv library is hosted at <http://github.com/LeventErkok/sbv>.
-- Comments, bug reports, and patches are always welcome.)
--
-- SBV: SMT Based Verification
--
-- Express properties about Haskell programs and automatically prove
-- them using SMT solvers.
--
-- >>> prove $ \x -> x `shiftL` 2 .== 4 * (x :: SWord8)
-- Q.E.D.
--
-- >>> prove $ forAll ["x"] $ \x -> x `shiftL` 2 .== (x :: SWord8)
-- Falsifiable. Counter-example:
--   x = 51 :: SWord8
--
-- The function 'prove' has the following type:
--
-- @
--     'prove' :: 'Provable' a => a -> 'IO' 'ThmResult'
-- @
--
-- The class 'Provable' comes with instances for n-ary predicates, for arbitrary n.
-- The predicates are just regular Haskell functions over symbolic signed and unsigned
-- bit-vectors. Functions for checking satisfiability ('sat' and 'allSat') are also
-- provided.
--
-- In particular, the sbv library introduces the types:
--
--   * 'SBool': Symbolic Booleans (bits).
--
--   * 'SWord8', 'SWord16', 'SWord32', 'SWord64': Symbolic Words (unsigned).
--
--   * 'SInt8',  'SInt16',  'SInt32',  'SInt64': Symbolic Ints (signed).
--
--   * 'SInteger': Unbounded signed integers.
--
--   * 'SReal': Algebraic-real numbers
--
--   * 'SFloat': IEEE-754 single-precision floating point values
--
--   * 'SDouble': IEEE-754 double-precision floating point values
--
--   * 'SArray', 'SFunArray': Flat arrays of symbolic values.
--
--   * Symbolic polynomials over GF(2^n), polynomial arithmetic, and CRCs.
--
--   * Uninterpreted constants and functions over symbolic values, with user
--     defined SMT-Lib axioms.
--
--   * Uninterpreted sorts, and proofs over such sorts, potentially with axioms.
--
-- The user can construct ordinary Haskell programs using these types, which behave
-- very similar to their concrete counterparts. In particular these types belong to the
-- standard classes 'Num', 'Bits', custom versions of 'Eq' ('EqSymbolic') 
-- and 'Ord' ('OrdSymbolic'), along with several other custom classes for simplifying
-- programming with symbolic values. The framework takes full advantage of Haskell's type
-- inference to avoid many common mistakes.
--
-- Furthermore, predicates (i.e., functions that return 'SBool') built out of
-- these types can also be:
--
--   * proven correct via an external SMT solver (the 'prove' function)
--
--   * checked for satisfiability (the 'sat', 'allSat' functions)
--
--   * used in synthesis (the `sat` function with existentials)
--
--   * quick-checked
--
-- If a predicate is not valid, 'prove' will return a counterexample: An
-- assignment to inputs such that the predicate fails. The 'sat' function will
-- return a satisfying assignment, if there is one. The 'allSat' function returns
-- all satisfying assignments, lazily.
--
-- The sbv library uses third-party SMT solvers via the standard SMT-Lib interface:
-- <http://goedel.cs.uiowa.edu/smtlib/>.
--
-- The SBV library is designed to work with any SMT-Lib compliant SMT-solver.
-- Currently, we support the following SMT-Solvers out-of-the box:
--
--   * Z3 from Microsoft: <http://research.microsoft.com/en-us/um/redmond/projects/z3/>
--
--   * Yices from SRI: <http://yices.csl.sri.com/>
--
--   * CVC4 from New York University and University of Iowa: <http://cvc4.cs.nyu.edu/>
--
--   * Boolector from Johannes Kepler University: <http://fmv.jku.at/boolector/>
--
--   * MathSAT from Fondazione Bruno Kessler and DISI-University of Trento: <http://mathsat.fbk.eu/>
--
-- SBV also allows calling these solvers in parallel, either getting results from multiple solvers
-- or returning the fastest one. (See 'proveWithAll', 'proveWithAny', etc.)
--
-- Support for other compliant solvers can be added relatively easily, please
-- get in touch if there is a solver you'd like to see included.
---------------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}

module Data.SBV (
  -- * Programming with symbolic values
  -- $progIntro

  -- ** Symbolic types

  -- *** Symbolic bit
    SBool
  -- *** Unsigned symbolic bit-vectors
  , SWord8, SWord16, SWord32, SWord64
  -- *** Signed symbolic bit-vectors
  , SInt8, SInt16, SInt32, SInt64
  -- *** Signed unbounded integers
  -- $unboundedLimitations
  , SInteger
  -- *** IEEE-floating point numbers
  -- $floatingPoints
  , SFloat, SDouble, RoundingMode(..), nan, infinity, sNaN, sInfinity, fusedMA, isSNaN, isFPPoint
  -- *** Signed algebraic reals
  -- $algReals
  , SReal, AlgReal, toSReal
  -- ** Creating a symbolic variable
  -- $createSym
  , sBool, sWord8, sWord16, sWord32, sWord64, sInt8, sInt16, sInt32, sInt64, sInteger, sReal, sFloat, sDouble
  -- ** Creating a list of symbolic variables
  -- $createSyms
  , sBools, sWord8s, sWord16s, sWord32s, sWord64s, sInt8s, sInt16s, sInt32s, sInt64s, sIntegers, sReals, sFloats, sDoubles
  -- *** Abstract SBV type
  , SBV
  -- *** Arrays of symbolic values
  , SymArray(..), SArray, SFunArray, mkSFunArray
  -- *** Full binary trees
  , STree, readSTree, writeSTree, mkSTree
  -- ** Operations on symbolic values
  -- *** Word level
  , sbvTestBit, sbvPopCount, sbvShiftLeft, sbvShiftRight, sbvSignedShiftArithRight, setBitTo, oneIf, lsb, msb
  , sbvRotateLeft, sbvRotateRight
  -- *** Predicates
  , allEqual, allDifferent, inRange, sElem
  -- *** Addition and Multiplication with high-bits
  , fullAdder, fullMultiplier
  -- *** Blasting/Unblasting
  , blastBE, blastLE, FromBits(..)
  -- *** Splitting, joining, and extending
  , Splittable(..)
  -- *** Sign-casting
  , SignCast(..)
  -- ** Polynomial arithmetic and CRCs
  , Polynomial(..), crcBV, crc
  -- ** Conditionals: Mergeable values
  , Mergeable(..)
  -- ** Symbolic equality
  , EqSymbolic(..)
  -- ** Symbolic ordering
  , OrdSymbolic(..)
  -- ** Symbolic integral numbers
  , SIntegral
  -- ** Division
  , SDivisible(..)
  -- ** The Boolean class
  , Boolean(..)
  -- *** Generalizations of boolean operations
  , bAnd, bOr, bAny, bAll
  -- ** Pretty-printing and reading numbers in Hex & Binary
  , PrettyNum(..), readBin

  -- * Uninterpreted sorts, constants, and functions
  -- $uninterpreted
  , Uninterpreted(..), addAxiom

  -- * Properties, proofs, and satisfiability
  -- $proveIntro

  -- ** Predicates
  , Predicate, Provable(..), Equality(..)
  -- ** Proving properties
  , prove, proveWith, isTheorem, isTheoremWith
  -- ** Checking satisfiability
  , sat, satWith, isSatisfiable, isSatisfiableWith
  -- ** Finding all satisfying assignments
  , allSat, allSatWith
  -- ** Satisfying a sequence of boolean conditions
  , solve
  -- ** Adding constraints
  -- $constrainIntro
  , constrain, pConstrain
  -- ** Checking constraint vacuity
  , isVacuous, isVacuousWith

  -- * Proving properties using multiple solvers
  -- $multiIntro
  , proveWithAll, proveWithAny, satWithAll, satWithAny, allSatWithAll, allSatWithAny

  -- * Optimization
  -- $optimizeIntro
  , minimize, maximize, optimize
  , minimizeWith, maximizeWith, optimizeWith

  -- * Computing expected values
  , expectedValue, expectedValueWith

  -- * Model extraction
  -- $modelExtraction

  -- ** Inspecting proof results
  -- $resultTypes
  , ThmResult(..), SatResult(..), AllSatResult(..), SMTResult(..)

  -- ** Programmable model extraction
  -- $programmableExtraction
  , SatModel(..), Modelable(..), displayModels, extractModels
  , getModelDictionaries, getModelValues, getModelUninterpretedValues

  -- * SMT Interface: Configurations and solvers
  , SMTConfig(..), SMTLibLogic(..), Logic(..), OptimizeOpts(..), Solver(..), SMTSolver(..), boolector, cvc4, yices, z3, mathSAT, sbvCurrentSolver, defaultSMTCfg, sbvCheckSolverInstallation, sbvAvailableSolvers

  -- * Symbolic computations
  , Symbolic, output, SymWord(..)

  -- * Getting SMT-Lib output (for offline analysis)
  , compileToSMTLib, generateSMTBenchmarks

  -- * Test case generation
  , genTest, getTestValues, TestVectors, TestStyle(..), renderTest, CW(..), HasKind(..), Kind(..), cwToBool

  -- * Code generation from symbolic programs
  -- $cCodeGeneration
  , SBVCodeGen

  -- ** Setting code-generation options
  , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile

  -- ** Designating inputs
  , cgInput, cgInputArr

  -- ** Designating outputs
  , cgOutput, cgOutputArr

  -- ** Designating return values
  , cgReturn, cgReturnArr

  -- ** Code generation with uninterpreted functions
  , cgAddPrototype, cgAddDecl, cgAddLDFlags

  -- ** Code generation with 'SInteger' and 'SReal' types
  -- $unboundedCGen
  , cgIntegerSize, cgSRealType, CgSRealType(..)

  -- ** Compilation to C
  , compileToC, compileToCLib

  -- * Module exports
  -- $moduleExportIntro

  , module Data.Bits
  , module Data.Word
  , module Data.Int
  , module Data.Ratio
  ) where

import Control.Monad            (filterM)
import Control.Concurrent.Async (async, waitAny, waitAnyCancel)
import System.IO.Unsafe         (unsafeInterleaveIO)             -- only used safely!

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.BitVectors.SignCast
import Data.SBV.BitVectors.Splittable
import Data.SBV.BitVectors.STree
import Data.SBV.Compilers.C
import Data.SBV.Compilers.CodeGen
import Data.SBV.Provers.Prover
import Data.SBV.Tools.GenTest
import Data.SBV.Tools.ExpectedValue
import Data.SBV.Tools.Optimize
import Data.SBV.Tools.Polynomial
import Data.SBV.Utils.Boolean
import Data.Bits
import Data.Int
import Data.Ratio
import Data.Word

-- | The currently active solver, obtained by importing "Data.SBV".
-- To have other solvers /current/, import one of the bridge
-- modules "Data.SBV.Bridge.CVC4", "Data.SBV.Bridge.Yices", or
-- "Data.SBV.Bridge.Z3" directly.
sbvCurrentSolver :: SMTConfig
sbvCurrentSolver = z3

-- | Note that the floating point value NaN does not compare equal to itself,
-- so we need a special recognizer for that. Haskell provides the isNaN predicate
-- with the `RealFrac` class, which unfortunately is not currently implementable for
-- symbolic cases. (Requires trigonometric functions etc.) Thus, we provide this
-- recognizer separately. Note that the definition simply tests equality against
-- itself, which fails for NaN. Who said equality for floating point was reflexive?
isSNaN :: (Floating a, SymWord a) => SBV a -> SBool
isSNaN x = x ./= x

-- | We call a FP number FPPoint if it is neither NaN, nor +/- infinity.
isFPPoint :: (Floating a, SymWord a) => SBV a -> SBool
isFPPoint x =     x .== x           -- gets rid of NaN's
              &&& x .< sInfinity    -- gets rid of +inf
              &&& x .> -sInfinity   -- gets rid of -inf

-- | Form the symbolic conjunction of a given list of boolean conditions. Useful in expressing
-- problems with constraints, like the following:
--
-- @
--   do [x, y, z] <- sIntegers [\"x\", \"y\", \"z\"]
--      solve [x .> 5, y + z .< x]
-- @
solve :: [SBool] -> Symbolic SBool
solve = return . bAnd

-- | Check whether the given solver is installed and is ready to go. This call does a
-- simple call to the solver to ensure all is well.
sbvCheckSolverInstallation :: SMTConfig -> IO Bool
sbvCheckSolverInstallation cfg = do ThmResult r <- proveWith cfg $ \x -> (x+x) .== ((x*2) :: SWord8)
                                    case r of
                                      Unsatisfiable _ -> return True
                                      _               -> return False

-- The default configs
defaultSolverConfig :: Solver -> SMTConfig
defaultSolverConfig Z3        = z3
defaultSolverConfig Yices     = yices
defaultSolverConfig Boolector = boolector
defaultSolverConfig CVC4      = cvc4
defaultSolverConfig MathSAT   = mathSAT

-- | Return the known available solver configs, installed on your machine.
sbvAvailableSolvers :: IO [SMTConfig]
sbvAvailableSolvers = filterM sbvCheckSolverInstallation (map defaultSolverConfig [minBound .. maxBound])

sbvWithAny :: Provable a => [SMTConfig] -> (SMTConfig -> a -> IO b) -> a -> IO (Solver, b)
sbvWithAny []      _    _ = error "SBV.withAny: No solvers given!"
sbvWithAny solvers what a = snd `fmap` (mapM try solvers >>= waitAnyCancel)
   where try s = async $ what s a >>= \r -> return (name (solver s), r)

sbvWithAll :: Provable a => [SMTConfig] -> (SMTConfig -> a -> IO b) -> a -> IO [(Solver, b)]
sbvWithAll solvers what a = mapM try solvers >>= (unsafeInterleaveIO . go)
   where try s = async $ what s a >>= \r -> return (name (solver s), r)
         go []  = return []
         go as  = do (d, r) <- waitAny as
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     return (r : rs)

-- | Prove a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
proveWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, ThmResult)]
proveWithAll  = (`sbvWithAll` proveWith)

-- | Prove a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
proveWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, ThmResult)
proveWithAny  = (`sbvWithAny` proveWith)

-- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
satWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, SatResult)]
satWithAll = (`sbvWithAll` satWith)

-- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
satWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, SatResult)
satWithAny    = (`sbvWithAny` satWith)

-- | Find all satisfying assignments to a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
allSatWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, AllSatResult)]
allSatWithAll = (`sbvWithAll` allSatWith)

-- | Find all satisfying assignments to a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
allSatWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, AllSatResult)
allSatWithAny = (`sbvWithAny` allSatWith)

-- | Equality as a proof method. Allows for
-- very concise construction of equivalence proofs, which is very typical in
-- bit-precise proofs.
infix 4 ===
class Equality a where
  (===) :: a -> a -> IO ThmResult

instance (SymWord a, EqSymbolic z) => Equality (SBV a -> z) where
  k === l = prove $ \a -> k a .== l a

instance (SymWord a, SymWord b, EqSymbolic z) => Equality (SBV a -> SBV b -> z) where
  k === l = prove $ \a b -> k a b .== l a b

instance (SymWord a, SymWord b, EqSymbolic z) => Equality ((SBV a, SBV b) -> z) where
  k === l = prove $ \a b -> k (a, b) .== l (a, b)

instance (SymWord a, SymWord b, SymWord c, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> z) where
  k === l = prove $ \a b c -> k a b c .== l a b c

instance (SymWord a, SymWord b, SymWord c, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c) -> z) where
  k === l = prove $ \a b c -> k (a, b, c) .== l (a, b, c)

instance (SymWord a, SymWord b, SymWord c, SymWord d, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> z) where
  k === l = prove $ \a b c d -> k a b c d .== l a b c d

instance (SymWord a, SymWord b, SymWord c, SymWord d, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d) -> z) where
  k === l = prove $ \a b c d -> k (a, b, c, d) .== l (a, b, c, d)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> z) where
  k === l = prove $ \a b c d e -> k a b c d e .== l a b c d e

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e) -> z) where
  k === l = prove $ \a b c d e -> k (a, b, c, d, e) .== l (a, b, c, d, e)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> z) where
  k === l = prove $ \a b c d e f -> k a b c d e f .== l a b c d e f

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> z) where
  k === l = prove $ \a b c d e f -> k (a, b, c, d, e, f) .== l (a, b, c, d, e, f)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g -> z) where
  k === l = prove $ \a b c d e f g -> k a b c d e f g .== l a b c d e f g

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> z) where
  k === l = prove $ \a b c d e f g -> k (a, b, c, d, e, f, g) .== l (a, b, c, d, e, f, g)

-- Haddock section documentation
{- $progIntro
The SBV library is really two things:

  * A framework for writing symbolic programs in Haskell, i.e., programs operating on
    symbolic values along with the usual concrete counterparts.

  * A framework for proving properties of such programs using SMT solvers.

The programming goal of SBV is to provide a /seamless/ experience, i.e., let people program
in the usual Haskell style without distractions of symbolic coding. While Haskell helps
in some aspects (the 'Num' and 'Bits' classes simplify coding), it makes life harder
in others. For instance, @if-then-else@ only takes 'Bool' as a test in Haskell, and
comparisons ('>' etc.) only return 'Bool's. Clearly we would like these values to be
symbolic (i.e., 'SBool'), thus stopping us from using some native Haskell constructs.
When symbolic versions of operators are needed, they are typically obtained by prepending a dot,
for instance '==' becomes '.=='. Care has been taken to make the transition painless. In
particular, any Haskell program you build out of symbolic components is fully concretely
executable within Haskell, without the need for any custom interpreters. (They are truly
Haskell programs, not AST's built out of pieces of syntax.) This provides for an integrated
feel of the system, one of the original design goals for SBV.
-}

{- $proveIntro
The SBV library provides a "push-button" verification system via automated SMT solving. The
design goal is to let SMT solvers be used without any knowledge of how SMT solvers work
or how different logics operate. The details are hidden behind the SBV framework, providing
Haskell programmers with a clean API that is unencumbered by the details of individual solvers.
To that end, we use the SMT-Lib standard (<http://goedel.cs.uiowa.edu/smtlib/>)
to communicate with arbitrary SMT solvers.
-}

{- $multiIntro
On a multi-core machine, it might be desirable to try a given property using multiple SMT solvers,
using parallel threads. Even with machines with single-cores, threading can be helpful if you
want to try out multiple-solvers but do not know which one would work the best
for the problem at hand ahead of time.

The functions in this section allow proving/satisfiability-checking with multiple
backends at the same time. Each function comes in two variants, one that
returns the results from all solvers, the other that returns the fastest one.

The @All@ variants, (i.e., 'proveWithAll', 'satWithAll', 'allSatWithAll') run all solvers and
return all the results. SBV internally makes sure that the result is lazily generated; so,
the order of solvers given does not matter. In other words, the order of results will follow
the order of the solvers as they finish, not as given by the user. These variants are useful when you
want to make sure multiple-solvers agree (or disagree!) on a given problem.

The @Any@ variants, (i.e., 'proveWithAny', 'satWithAny', 'allSatWithAny') will run all the solvers
in parallel, and return the results of the first one finishing. The other threads will then be killed. These variants
are useful when you do not care if the solvers produce the same result, but rather want to get the
solution as quickly as possible, taking advantage of modern many-core machines.

Note that the function 'sbvAvailableSolvers' will return all the installed solvers, which can be
used as the first argument to all these functions, if you simply want to try all available solvers on a machine.
-}

{- $optimizeIntro
Symbolic optimization. A call of the form:

    @minimize Quantified cost n valid@

returns @Just xs@, such that:

   * @xs@ has precisely @n@ elements

   * @valid xs@ holds

   * @cost xs@ is minimal. That is, for all sequences @ys@ that satisfy the first two criteria above, @cost xs .<= cost ys@ holds.

If there is no such sequence, then 'minimize' will return 'Nothing'.

The function 'maximize' is similar, except the comparator is '.>='. So the value returned has the largest cost (or value, in that case).

The function 'optimize' allows the user to give a custom comparison function.

The 'OptimizeOpts' argument controls how the optimization is done. If 'Quantified' is used, then the SBV optimization engine satisfies the following predicate:

   @exists xs. forall ys. valid xs && (valid ys ``implies`` (cost xs ``cmp`` cost ys))@

Note that this may cause efficiency problems as it involves alternating quantifiers.
If 'OptimizeOpts' is set to 'Iterative' 'True', then SBV will programmatically
search for an optimal solution, by repeatedly calling the solver appropriately. (The boolean argument controls whether progress reports are given. Use
'False' for quiet operation.) Note that the quantified and iterative versions are two different optimization approaches and may not necessarily yield the same
results. In particular, the quantified version can find solutions where there is no global optimum value, while the iterative version would simply loop forever
in such cases. On the other hand, the iterative version might be more suitable if the quantified version of the problem is too hard to deal with by the SMT solver.
-}

{- $modelExtraction
The default 'Show' instances for prover calls provide all the counter-example information in a
human-readable form and should be sufficient for most casual uses of sbv. However, tools built
on top of sbv will inevitably need to look into the constructed models more deeply, programmatically
extracting their results and performing actions based on them. The API provided in this section
aims at simplifying this task.
-}

{- $resultTypes
'ThmResult', 'SatResult', and 'AllSatResult' are simple newtype wrappers over 'SMTResult'. Their
main purpose is so that we can provide custom 'Show' instances to print results accordingly.
-}

{- $programmableExtraction
While default 'Show' instances are sufficient for most use cases, it is sometimes desirable (especially
for library construction) that the SMT-models are reinterpreted in terms of domain types. Programmable
extraction allows getting arbitrarily typed models out of SMT models.
-}

{- $cCodeGeneration
The SBV library can generate straight-line executable code in C. (While other target languages are
certainly possible, currently only C is supported.) The generated code will perform no run-time memory-allocations,
(no calls to @malloc@), so its memory usage can be predicted ahead of time. Also, the functions will execute precisely the
same instructions in all calls, so they have predictable timing properties as well. The generated code
has no loops or jumps, and is typically quite fast. While the generated code can be large due to complete unrolling,
these characteristics make them suitable for use in hard real-time systems, as well as in traditional computing.
-}

{- $unboundedCGen
The types 'SInteger' and 'SReal' are unbounded quantities that have no direct counterparts in the C language. Therefore,
it is not possible to generate standard C code for SBV programs using these types, unless custom libraries are available. To
overcome this, SBV allows the user to explicitly set what the corresponding types should be for these two cases, using
the functions below. Note that while these mappings will produce valid C code, the resulting code will be subject to
overflow/underflows for 'SInteger', and rounding for 'SReal', so there is an implicit loss of precision.

If the user does /not/ specify these mappings, then SBV will
refuse to compile programs that involve these types.
-}

{- $moduleExportIntro
The SBV library exports the following modules wholesale, as user programs will have to import these
modules to make any sensible use of the SBV functionality.
-}

{- $createSym
These functions simplify declaring symbolic variables of various types. Strictly speaking, they are just synonyms
for 'free' (specialized at the given type), but they might be easier to use.
-}

{- $createSyms
These functions simplify declaring a sequence symbolic variables of various types. Strictly speaking, they are just synonyms
for 'mapM' 'free' (specialized at the given type), but they might be easier to use.
-}

{- $unboundedLimitations
The SBV library supports unbounded signed integers with the type 'SInteger', which are not subject to
overflow/underflow as it is the case with the bounded types, such as 'SWord8', 'SInt16', etc. However,
some bit-vector based operations are /not/ supported for the 'SInteger' type while in the verification mode. That
is, you can use these operations on 'SInteger' values during normal programming/simulation.
but the SMT translation will not support these operations since there corresponding operations are not supported in SMT-Lib.
Note that this should rarely be a problem in practice, as these operations are mostly meaningful on fixed-size
bit-vectors. The operations that are restricted to bounded word/int sizes are:

   * Rotations and shifts: 'rotateL', 'rotateR', 'shiftL', 'shiftR'

   * Bitwise logical ops: '.&.', '.|.', 'xor', 'complement'

   * Extraction and concatenation: 'split', '#', and 'extend' (see the 'Splittable' class)

Usual arithmetic ('+', '-', '*', 'sQuotRem', 'sQuot', 'sRem', 'sDivMod', 'sDiv', 'sMod') and logical operations ('.<', '.<=', '.>', '.>=', '.==', './=') operations are
supported for 'SInteger' fully, both in programming and verification modes.
-}

{- $algReals
Algebraic reals are roots of single-variable polynomials with rational coefficients. (See
<http://en.wikipedia.org/wiki/Algebraic_number>.) Note that algebraic reals are infinite
precision numbers, but they do not cover all /real/ numbers. (In particular, they cannot
represent transcendentals.) Some irrational numbers are algebraic (such as @sqrt 2@), while
others are not (such as pi and e).

SBV can deal with real numbers just fine, since the theory of reals is decidable. (See
<http://goedel.cs.uiowa.edu/smtlib/theories/Reals.smt2>.) In addition, by leveraging backend
solver capabilities, SBV can also represent and solve non-linear equations involving real-variables.
(For instance, the Z3 SMT solver, supports polynomial constraints on reals starting with v4.0.)
-}

{- $floatingPoints
Floating point numbers are defined by the IEEE-754 standard; and correspond to Haskell's
'Float' and 'Double' types. For SMT support with floating-point numbers, see the paper
by Rummer and Wahl: <http://www.philipp.ruemmer.org/publications/smt-fpa.pdf>.
-}

{- $constrainIntro
A constraint is a means for restricting the input domain of a formula. Here's a simple
example:

@
   do x <- 'exists' \"x\"
      y <- 'exists' \"y\"
      'constrain' $ x .> y
      'constrain' $ x + y .>= 12
      'constrain' $ y .>= 3
      ...
@

The first constraint requires @x@ to be larger than @y@. The scond one says that
sum of @x@ and @y@ must be at least @12@, and the final one says that @y@ to be at least @3@.
Constraints provide an easy way to assert additional properties on the input domain, right at the point of
the introduction of variables.

Note that the proper reading of a constraint
depends on the context:

    * In a 'sat' (or 'allSat') call: The constraint added is asserted
    conjunctively. That is, the resulting satisfying model (if any) will
    always satisfy all the constraints given.

  * In a 'prove' call: In this case, the constraint acts as an implication.
    The property is proved under the assumption that the constraint
    holds. In other words, the constraint says that we only care about
    the input space that satisfies the constraint.

  * In a 'quickCheck' call: The constraint acts as a filter for 'quickCheck';
    if the constraint does not hold, then the input value is considered to be irrelevant
    and is skipped. Note that this is similar to 'prove', but is stronger: We do not
    accept a test case to be valid just because the constraints fail on them, although
    semantically the implication does hold. We simply skip that test case as a /bad/
    test vector.

  * In a 'genTest' call: Similar to 'quickCheck' and 'prove': If a constraint
    does not hold, the input value is ignored and is not included in the test
    set.

A good use case (in fact the motivating use case) for 'constrain' is attaching a
constraint to a 'forall' or 'exists' variable at the time of its creation.
Also, the conjunctive semantics for 'sat' and the implicative
semantics for 'prove' simplify programming by choosing the correct interpretation
automatically. However, one should be aware of the semantic difference. For instance, in
the presence of constraints, formulas that are /provable/ are not necessarily
/satisfiable/. To wit, consider:

 @
    do x <- 'exists' \"x\"
       'constrain' $ x .< x
       return $ x .< (x :: 'SWord8')
 @

This predicate is unsatisfiable since no element of 'SWord8' is less than itself. But
it's (vacuously) true, since it excludes the entire domain of values, thus making the proof
trivial. Hence, this predicate is provable, but is not satisfiable. To make sure the given
constraints are not vacuous, the functions 'isVacuous' (and 'isVacuousWith') can be used.

Also note that this semantics imply that test case generation ('genTest') and quick-check
can take arbitrarily long in the presence of constraints, if the random input values generated
rarely satisfy the constraints. (As an extreme case, consider @'constrain' 'false'@.)

A probabilistic constraint (see 'pConstrain') attaches a probability threshold for the
constraint to be considered. For instance:

  @
     'pConstrain' 0.8 c
  @

will make sure that the condition @c@ is satisfied 80% of the time (and correspondingly, falsified 20%
of the time), in expectation. This variant is useful for 'genTest' and 'quickCheck' functions, where we
want to filter the test cases according to some probability distribution, to make sure that the test-vectors
are drawn from interesting subsets of the input space. For instance, if we were to generate 100 test cases
with the above constraint, we'd expect about 80 of them to satisfy the condition @c@, while about 20 of them
will fail it.

The following properties hold:

  @
    'constrain'      = 'pConstrain' 1
    'pConstrain' t c = 'pConstrain' (1-t) (not c)
  @

Note that while 'constrain' can be used freely, 'pConstrain' is only allowed in the contexts of
'genTest' or 'quickCheck'. Calls to 'pConstrain' in a prove/sat call will be rejected as SBV does not
deal with probabilistic constraints when it comes to satisfiability and proofs.
Also, both 'constrain' and 'pConstrain' calls during code-generation will also be rejected, for similar reasons.
-}

{- $uninterpreted
Users can introduce new uninterpreted sorts simply by defining a data-type in Haskell and registering it as such. The
following example demonstrates:

  @
     data B = B deriving (Eq, Ord, Data, Typeable)
     instance SymWord  B
     instance HasKind  B
  @

(Note that you'll also need to use the language pragma @DeriveDataTypeable@, and import @Data.Generics@ for the above to work.) 

Once GHC implements derivable user classes (<http://hackage.haskell.org/trac/ghc/ticket/5462>), we will be able to simplify this to:

  @
     data B = B deriving (Eq, Ord, Data, Typeable, SymWord, HasKind)
  @

This is all it takes to introduce 'B' as an uninterpreted sort in SBV, which makes the type @SBV B@ automagically become available as the type
of symbolic values that ranges over 'B' values.

Uninterpreted functions over both uninterpreted and regular sorts can be declared using the facilities introduced by
the 'Uninterpreted' class.
-}

{-# ANN module "HLint: ignore Use import/export shortcut" #-}

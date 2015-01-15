-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Conversion of symbolic programs to SMTLib format
-----------------------------------------------------------------------------

module Data.SBV.SMT.SMTLib(SMTLibPgm, SMTLibConverter, toSMTLib1, toSMTLib2, addNonEqConstraints, interpretSolverOutput, interpretSolverModelLine) where

import Data.Char (isDigit)

import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import qualified Data.SBV.SMT.SMTLib1 as SMT1
import qualified Data.SBV.SMT.SMTLib2 as SMT2

import qualified Data.Set as Set (Set, member, toList)

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibConverter =  RoundingMode                -- ^ User selected rounding mode to be used for floating point arithmetic
                     -> Maybe Logic                 -- ^ User selected logic to use. If Nothing, pick automatically.
                     -> SolverCapabilities          -- ^ Capabilities of the backend solver targeted
                     -> Set.Set Kind                -- ^ Kinds used in the problem
                     -> Bool                        -- ^ is this a sat problem?
                     -> [String]                    -- ^ extra comments to place on top
                     -> [(Quantifier, NamedSymVar)] -- ^ inputs and aliasing names
                     -> [Either SW (SW, [SW])]      -- ^ skolemized inputs
                     -> [(SW, CW)]                  -- ^ constants
                     -> [((Int, Kind, Kind), [SW])] -- ^ auto-generated tables
                     -> [(Int, ArrayInfo)]          -- ^ user specified arrays
                     -> [(String, SBVType)]         -- ^ uninterpreted functions/constants
                     -> [(String, [String])]        -- ^ user given axioms
                     -> SBVPgm                      -- ^ assignments
                     -> [SW]                        -- ^ extra constraints
                     -> SW                          -- ^ output variable
                     -> SMTLibPgm

-- | Convert to SMTLib-1 format
toSMTLib1 :: SMTLibConverter

-- | Convert to SMTLib-2 format
toSMTLib2 :: SMTLibConverter
(toSMTLib1, toSMTLib2) = (cvt SMTLib1, cvt SMTLib2)
  where cvt v roundMode smtLogic solverCaps kindInfo isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out
         | KUnbounded `Set.member` kindInfo && not (supportsUnboundedInts solverCaps)
         = unsupported "unbounded integers"
         | KReal `Set.member` kindInfo  && not (supportsReals solverCaps)
         = unsupported "algebraic reals"
         | needsFloats && not (supportsFloats solverCaps)
         = unsupported "single-precision floating-point numbers"
         | needsDoubles && not (supportsDoubles solverCaps)
         = unsupported "double-precision floating-point numbers"
         | needsQuantifiers && not (supportsQuantifiers solverCaps)
         = unsupported "quantifiers"
         | not (null sorts) && not (supportsUninterpretedSorts solverCaps)
         = unsupported "uninterpreted sorts"
         | True
         = SMTLibPgm v (aliasTable, pre, post)
         where sorts = [s | KUserSort s _ <- Set.toList kindInfo]
               unsupported w = error $ "SBV: Given problem needs " ++ w ++ ", which is not supported by SBV for the chosen solver: " ++ capSolverName solverCaps
               aliasTable  = map (\(_, (x, y)) -> (y, x)) qinps
               converter   = if v == SMTLib1 then SMT1.cvt else SMT2.cvt
               (pre, post) = converter roundMode smtLogic solverCaps kindInfo isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out
               needsFloats  = KFloat  `Set.member` kindInfo
               needsDoubles = KDouble `Set.member` kindInfo
               needsQuantifiers
                 | isSat = ALL `elem` quantifiers
                 | True  = EX  `elem` quantifiers
                 where quantifiers = map fst qinps

-- | Add constraints generated from older models, used for querying new models
addNonEqConstraints :: RoundingMode -> [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> SMTLibPgm -> Maybe String
addNonEqConstraints rm _qinps cs p@(SMTLibPgm SMTLib1 _) = SMT1.addNonEqConstraints rm cs p
addNonEqConstraints rm  qinps cs p@(SMTLibPgm SMTLib2 _) = SMT2.addNonEqConstraints rm qinps cs p

-- | Interpret solver output based on SMT-Lib standard output responses
interpretSolverOutput :: SMTConfig -> ([String] -> SMTModel) -> [String] -> SMTResult
interpretSolverOutput cfg _          ("unsat":_)      = Unsatisfiable cfg
interpretSolverOutput cfg extractMap ("unknown":rest) = Unknown       cfg  $ extractMap rest
interpretSolverOutput cfg extractMap ("sat":rest)     = Satisfiable   cfg  $ extractMap rest
interpretSolverOutput cfg _          ("timeout":_)    = TimeOut       cfg
interpretSolverOutput cfg _          ls               = ProofError    cfg  ls

-- | Get a counter-example from an SMT-Lib2 like model output line
-- This routing is necessarily fragile as SMT solvers tend to print output
-- in whatever form they deem convenient for them.. Currently, it's tuned to
-- work with Z3 and CVC4; if new solvers are added, we might need to rework
-- the logic here.
interpretSolverModelLine :: [NamedSymVar] -> String -> [(Int, (String, CW))]
interpretSolverModelLine inps line = either err extract (parseSExpr line)
  where err r =  error $  "*** Failed to parse SMT-Lib2 model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"
        getInput (ECon v)            = isInput v
        getInput (EApp (ECon v : _)) = isInput v
        getInput _                   = Nothing
        isInput ('s':v)
          | all isDigit v = let inpId :: Int
                                inpId = read v
                            in case [(s, nm) | (s@(SW _ (NodeId n)), nm) <-  inps, n == inpId] of
                                 []        -> Nothing
                                 [(s, nm)] -> Just (inpId, s, nm)
                                 matches -> error $  "SBV.SMTLib2: Cannot uniquely identify value for "
                                                  ++ 's':v ++ " in "  ++ show matches
        isInput _       = Nothing
        getUIIndex (KUserSort  _ (Right xs, _)) i = i `lookup` zip xs [0..]
        getUIIndex _                                 _ = Nothing
        extract (EApp [EApp [v, ENum    i]]) | Just (n, s, nm) <- getInput v                    = [(n, (nm, mkConstCW (kindOf s) i))]
        extract (EApp [EApp [v, EReal   i]]) | Just (n, s, nm) <- getInput v, isReal s          = [(n, (nm, CW KReal (CWAlgReal i)))]
        extract (EApp [EApp [v, ECon    i]]) | Just (n, s, nm) <- getInput v, isUninterpreted s = let k = kindOf s in [(n, (nm, CW k (CWUserSort (getUIIndex k i, i))))]
        extract (EApp [EApp [v, EDouble i]]) | Just (n, s, nm) <- getInput v, isDouble s        = [(n, (nm, CW KDouble (CWDouble i)))]
        extract (EApp [EApp [v, EFloat  i]]) | Just (n, s, nm) <- getInput v, isFloat s         = [(n, (nm, CW KFloat (CWFloat i)))]
        -- weird lambda app that CVC4 seems to throw out.. logic below derived from what I saw CVC4 print, hopefully sufficient
        extract (EApp (EApp (v : EApp (ECon "LAMBDA" : xs) : _) : _)) | Just{} <- getInput v, not (null xs) = extract (EApp [EApp [v, last xs]])
        extract (EApp [EApp (v : r)])      | Just (_, _, nm) <- getInput v = error $   "SBV.SMTLib2: Cannot extract value for " ++ show nm
                                                                                   ++ "\n\tInput: " ++ show line
                                                                                   ++ "\n\tParse: " ++  show r
        extract _                                                          = []

{-# ANN interpretSolverModelLine  "HLint: ignore Use elemIndex" #-}

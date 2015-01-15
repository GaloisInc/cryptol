-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Z3
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Z3 SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Z3(z3) where

import qualified Control.Exception as C

import Data.Char          (toLower)
import Data.Function      (on)
import Data.List          (sortBy, intercalate, isPrefixOf, groupBy)
import System.Environment (getEnv)
import qualified System.Info as S(os)

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- Choose the correct prefix character for passing options
-- TBD: Is there a more foolproof way of determining this?
optionPrefix :: Char
optionPrefix
  | map toLower S.os `elem` ["linux", "darwin"] = '-'
  | True                                        = '/'   -- windows

-- | The description of the Z3 SMT solver
-- The default executable is @\"z3\"@, which must be in your path. You can use the @SBV_Z3@ environment variable to point to the executable on your system.
-- The default options are @\"-in -smt2\"@, which is valid for Z3 4.1. You can use the @SBV_Z3_OPTIONS@ environment variable to override the options.
z3 :: SMTSolver
z3 = SMTSolver {
           name           = Z3
         , executable     = "z3"
         , options        = map (optionPrefix:) ["in", "smt2"]
         , engine         = \cfg isSat qinps modelMap skolemMap pgm -> do
                                    execName <-               getEnv "SBV_Z3"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (words `fmap` getEnv "SBV_Z3_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts} }
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        dlim = printRealPrec cfg'
                                        ppDecLim = "(set-option :pp.decimal_precision " ++ show dlim ++ ")\n"
                                        script = SMTScript {scriptBody = tweaks ++ ppDecLim ++ pgm, scriptModel = Just (cont (roundingMode cfg) skolemMap)}
                                    if dlim < 1
                                       then error $ "SBV.Z3: printRealPrec value should be at least 1, invalid value received: " ++ show dlim
                                       else standardSolver cfg' script cleanErrs (ProofError cfg') (interpretSolverOutput cfg' (extractMap isSat qinps modelMap))
         , xformExitCode  = id
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "Z3"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = True
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = True
                                , supportsUninterpretedSorts = True
                                , supportsUnboundedInts      = True
                                , supportsReals              = True
                                , supportsFloats             = True
                                , supportsDoubles            = True
                                }
         }
 where cleanErrs = intercalate "\n" . filter (not . junk) . lines
       junk = ("WARNING:" `isPrefixOf`)
       zero :: RoundingMode -> Kind -> String
       zero _  KBool                = "false"
       zero _  (KBounded _     sz)  = "#x" ++ replicate (sz `div` 4) '0'
       zero _  KUnbounded           = "0"
       zero _  KReal                = "0.0"
       zero rm KFloat               = showSMTFloat rm 0
       zero rm KDouble              = showSMTDouble rm 0
       -- For uninterpreted sorts, we use the first element of the enumerations if available; otherwise bail out..
       zero _  (KUserSort _ (Right (f:_), _)) = f
       zero _  (KUserSort s _)                = error $ "SBV.Z3.zero: Unexpected uninterpreted sort: " ++ s
       cont rm skolemMap = intercalate "\n" $ concatMap extract skolemMap
        where -- In the skolemMap:
              --    * Left's are universals: i.e., the model should be true for
              --      any of these. So, we simply "echo 0" for these values.
              --    * Right's are existentials. If there are no dependencies (empty list), then we can
              --      simply use get-value to extract it's value. Otherwise, we have to apply it to
              --      an appropriate number of 0's to get the final value.
              extract (Left s)        = ["(echo \"((" ++ show s ++ " " ++ zero rm (kindOf s) ++ "))\")"]
              extract (Right (s, [])) = let g = "(get-value (" ++ show s ++ "))" in getVal (kindOf s) g
              extract (Right (s, ss)) = let g = "(get-value ((" ++ show s ++ concat [' ' : zero rm (kindOf a) | a <- ss] ++ ")))" in getVal (kindOf s) g
              getVal KReal g = ["(set-option :pp.decimal false) " ++ g, "(set-option :pp.decimal true)  " ++ g]
              getVal _     g = [g]
       addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "Z3: Timeout value must be non-negative, received: " ++ show i
         | True                = o ++ [optionPrefix : "T:" ++ show i]

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap isSat qinps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ squashReals $ sortByNodeId $ concatMap (interpretSolverModelLine inps) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        inps -- for "sat", display the prefix existentials. For completeness, we will drop
             -- only the trailing foralls. Exception: Don't drop anything if it's all a sequence of foralls
             | isSat = map snd $ if all (== ALL) (map fst qinps)
                                 then qinps
                                 else reverse $ dropWhile ((== ALL) . fst) $ reverse qinps
             -- for "proof", just display the prefix universals
             | True  = map snd $ takeWhile ((== ALL) . fst) qinps
        squashReals :: [(Int, (String, CW))] -> [(Int, (String, CW))]
        squashReals = concatMap squash . groupBy ((==) `on` fst)
          where squash [(i, (n, cw1)), (_, (_, cw2))] = [(i, (n, mergeReals n cw1 cw2))]
                squash xs = xs
                mergeReals :: String -> CW -> CW -> CW
                mergeReals n (CW KReal (CWAlgReal a)) (CW KReal (CWAlgReal b)) = CW KReal (CWAlgReal (mergeAlgReals (bad n a b) a b))
                mergeReals n a b = bad n a b
                bad n a b = error $ "SBV.Z3: Cannot merge reals for variable: " ++ n ++ " received: " ++ show (a, b)

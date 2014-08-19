-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Boolector
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Boolector SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Boolector(boolector) where

import qualified Control.Exception as C

import Data.Function      (on)
import Data.List          (sortBy)
import System.Environment (getEnv)
import System.Exit        (ExitCode(..))

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the Boolector SMT solver
-- The default executable is @\"boolector\"@, which must be in your path. You can use the @SBV_BOOLECTOR@ environment variable to point to the executable on your system.
-- The default options are @\"-m --smt2\"@. You can use the @SBV_BOOLECTOR_OPTIONS@ environment variable to override the options.
boolector :: SMTSolver
boolector = SMTSolver {
           name           = Boolector
         , executable     = "boolector"
         , options        = ["-m", "--smt2"]
         , engine         = \cfg _isSat qinps modelMap _skolemMap pgm -> do
                                    execName <-               getEnv "SBV_BOOLECTOR"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (words `fmap` getEnv "SBV_BOOLECTOR_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts}
                                                   , satCmd = satCmd cfg ++ "\n(exit)" -- boolector requires a final exit line
                                                   }
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        -- boolector complains if we don't have "exit" at the end
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Nothing}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap (map snd qinps) modelMap))
         , xformExitCode  = boolectorExitCode
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "Boolector"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = False
                                , supportsProduceModels      = False
                                , supportsQuantifiers        = False
                                , supportsUninterpretedSorts = False
                                , supportsUnboundedInts      = False
                                , supportsReals              = False
                                , supportsFloats             = False
                                , supportsDoubles            = False
                                }
         }
 where addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "Boolector: Timeout value must be non-negative, received: " ++ show i
         | True                = o ++ ["-t=" ++ show i]

-- | Similar to CVC4, Boolector uses different exit codes to indicate its status.
boolectorExitCode :: ExitCode -> ExitCode
boolectorExitCode (ExitFailure n) | n `elem` [10, 20, 0] = ExitSuccess
boolectorExitCode ec                                     = ec

extractMap :: [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap inps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine inps . cvt) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        -- Boolector outputs in a non-parenthesized way; and also puts x's for don't care bits:
        cvt :: String -> String
        cvt s = case words s of
                  [var, val] -> "((" ++ var ++ " #b" ++ map tr val ++ "))"
                  _          -> s -- good-luck..
          where tr 'x' = '0'
                tr x   = x

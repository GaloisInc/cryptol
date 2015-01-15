-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.MathSAT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the MathSAT SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.MathSAT(mathSAT) where

import qualified Control.Exception as C

import Data.Function      (on)
import Data.List          (sortBy, intercalate)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the MathSAT SMT solver
-- The default executable is @\"mathsat\"@, which must be in your path. You can use the @SBV_MATHSAT@ environment variable to point to the executable on your system.
-- The default options are @\"-input=smt2\"@. You can use the @SBV_MATHSAT_OPTIONS@ environment variable to override the options.
mathSAT :: SMTSolver
mathSAT = SMTSolver {
           name           = MathSAT
         , executable     = "mathsat"
         , options        = ["-input=smt2"]
         , engine         = \cfg _isSat qinps modelMap skolemMap pgm -> do
                                    execName <-               getEnv "SBV_MATHSAT"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (words `fmap` getEnv "SBV_MATHSAT_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts}
                                                   }
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Just (cont skolemMap)}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap (map snd qinps) modelMap))
         , xformExitCode  = id
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "MathSAT"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = False
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = True
                                , supportsUninterpretedSorts = True
                                , supportsUnboundedInts      = True
                                , supportsReals              = True
                                , supportsFloats             = False
                                , supportsDoubles            = False
                                }
         }
 where zero :: Kind -> String
       zero KBool                = "false"
       zero (KBounded _     sz)  = "#x" ++ replicate (sz `div` 4) '0'
       zero KUnbounded           = "0"
       zero KReal                = "0.0"
       zero KFloat               = error "SBV.MathSAT.zero: Unexpected sort SFloat"
       zero KDouble              = error "SBV.MathSAT.zero: Unexpected sort SDouble"
       -- For uninterpreted sorts, we use the first element of the enumerations if available; otherwise bail out..
       zero (KUserSort _ (Right (f:_), _)) = f
       zero (KUserSort s _)                = error $ "SBV.MathSAT.zero: Unexpected uninterpreted sort: " ++ s
       cont skolemMap = intercalate "\n" $ concatMap extract skolemMap
        where -- In the skolemMap:
              --    * Left's are universals: i.e., the model should be true for
              --      any of these. So, we simply "echo 0" for these values.
              --    * Right's are existentials. If there are no dependencies (empty list), then we can
              --      simply use get-value to extract it's value. Otherwise, we have to apply it to
              --      an appropriate number of 0's to get the final value.
              extract (Left s)        = ["(echo \"((" ++ show s ++ " " ++ zero (kindOf s) ++ "))\")"]
              extract (Right (s, [])) = ["(get-value (" ++ show s ++ "))"]
              extract (Right (s, ss)) = let g = "(get-value ((" ++ show s ++ concat [' ' : zero (kindOf a) | a <- ss] ++ ")))" in [g]
       addTimeOut Nothing  o = o
       addTimeOut (Just _) _ = error "MathSAT: Timeout values are not supported by MathSat"

extractMap :: [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap inps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine inps . cvt) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        cvt :: String -> String
        cvt s = case words s of
                  [var, val] -> "((" ++ var ++ " #b" ++ map tr val ++ "))"
                  _          -> s -- good-luck..
          where tr 'x' = '0'
                tr x   = x

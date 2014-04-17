-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Yices
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Yices SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Yices(yices) where

import qualified Control.Exception as C

import Data.Char          (isDigit)
import Data.List          (sortBy, isPrefixOf, intercalate, transpose, partition)
import Data.Maybe         (mapMaybe, isNothing, fromJust)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the Yices SMT solver
-- The default executable is @\"yices-smt\"@, which must be in your path. You can use the @SBV_YICES@ environment variable to point to the executable on your system.
-- The default options are @\"-m -f\"@, which is valid for Yices 2.1 series. You can use the @SBV_YICES_OPTIONS@ environment variable to override the options.
yices :: SMTSolver
yices = SMTSolver {
           name           = "Yices"
         , executable     = "yices-smt"
         -- , options        = ["-tc", "-smt", "-e"]   -- For Yices1
         , options        = ["-m", "-f"]  -- For Yices2
         , engine         = \cfg _isSat qinps modelMap _skolemMap pgm -> do
                                    execName <-                getEnv "SBV_YICES"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (words `fmap`  getEnv "SBV_YICES_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg'   = cfg {solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts}}
                                        script = SMTScript {scriptBody = unlines (solverTweaks cfg') ++ pgm, scriptModel = Nothing}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap (map snd qinps) modelMap))
         , xformExitCode  = id
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "Yices"
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
          | i < 0               = error $ "Yices: Timeout value must be non-negative, received: " ++ show i
          | True                = o ++ ["-t", show i]

sortByNodeId :: [(Int, a)] -> [(Int, a)]
sortByNodeId = sortBy (\(x, _) (y, _) -> compare x y)

extractMap :: [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap inps modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (getCounterExample inps) modelLines
            , modelUninterps = [(n, ls) | (UFun _ n, ls) <- uis]
            , modelArrays    = [(n, ls) | (UArr _ n, ls) <- uis]
            }
  where (modelLines, unintLines) = moveConstUIs $ break ("--- " `isPrefixOf`) solverLines
        uis = extractUnints modelMap unintLines

-- another crude hack
moveConstUIs :: ([String], [String]) -> ([String], [String])
moveConstUIs (pre, post) = (pre', concatMap mkDecl extras ++ post)
  where (extras, pre') = partition ("(= uninterpreted_" `isPrefixOf`) pre
        mkDecl s = ["--- " ++ takeWhile (/= ' ') (drop 3 s) ++ " ---", s]

getCounterExample :: [NamedSymVar] -> String -> [(Int, (String, CW))]
getCounterExample inps line = either err extract (parseSExpr line)
  where err r =  error $  "*** Failed to parse Yices model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"
        isInput ('s':v)
          | all isDigit v = let inpId :: Int
                                inpId = read v
                            in case [(s, nm) | (s@(SW _ (NodeId n)), nm) <-  inps, n == inpId] of
                                 []        -> Nothing
                                 [(s, nm)] -> Just (inpId, s, nm)
                                 matches -> error $  "SBV.Yices: Cannot uniquely identify value for "
                                                  ++ 's':v ++ " in "  ++ show matches
        isInput _       = Nothing
        extract (EApp [ECon "=", ECon v, ENum i]) | Just (n, s, nm) <- isInput v = [(n, (nm, mkConstCW (kindOf s) i))]
        extract (EApp [ECon "=", ENum i, ECon v]) | Just (n, s, nm) <- isInput v = [(n, (nm, mkConstCW (kindOf s) i))]
        extract _                                                                = []

extractUnints :: [(String, UnintKind)] -> [String] -> [(UnintKind, [String])]
extractUnints modelMap = mapMaybe (extractUnint modelMap) . chunks
  where chunks []     = []
        chunks (x:xs) = let (f, r) = break ("---" `isPrefixOf`) xs in (x:f) : chunks r

-- Parsing the Yices output is done extremely crudely and designed
-- mostly by observation of Yices output. Likely to have bugs and
-- brittle as Yices evolves. We really need an SMT-Lib2 like interface.
extractUnint :: [(String, UnintKind)] -> [String] -> Maybe (UnintKind, [String])
extractUnint _    []           = Nothing
extractUnint mmap (tag : rest)
  | null tag'                  = Nothing
  | isNothing mbKnd            = Nothing
  | True                       = mapM (getUIVal knd) rest >>= \xs -> return (knd, format knd xs)
  where mbKnd | "--- uninterpreted_" `isPrefixOf` tag = uf `lookup` mmap
              | True                                  = af `lookup` mmap
        knd = fromJust mbKnd
        tag' = dropWhile (/= '_') tag
        f    = takeWhile (/= ' ') (tail tag')
        uf   = f
        af   = "array_" ++ f

getUIVal :: UnintKind -> String -> Maybe (String, [String], String)
getUIVal knd s
  | "default: " `isPrefixOf` s
  = getDefaultVal knd (dropWhile (/= ' ') s)
  | True
  = case parseSExpr s of
       Right (EApp [ECon "=", EApp (ECon _ : args), ENum i]) -> getCallVal knd args i
       Right (EApp [ECon "=", ECon _, ENum i])               -> getCallVal knd []   i
       _ -> Nothing

getDefaultVal :: UnintKind -> String -> Maybe (String, [String], String)
getDefaultVal knd n = case parseSExpr n of
                        Right (ENum i) -> Just $ showDefault knd (show i)
                        _               -> Nothing

getCallVal :: UnintKind -> [SExpr] -> Integer -> Maybe (String, [String], String)
getCallVal knd args res = mapM getArg args >>= \as -> return (showCall knd as (show res))

getArg :: SExpr -> Maybe String
getArg (ENum i) = Just (show i)
getArg _        = Nothing

showDefault :: UnintKind -> String -> (String, [String], String)
showDefault (UFun cnt f) res = (f, replicate cnt "_", res)
showDefault (UArr cnt f) res = (f, replicate cnt "_", res)

showCall :: UnintKind -> [String] -> String -> (String, [String], String)
showCall (UFun _ f) as res = (f, as, res)
showCall (UArr _ f) as res = (f, as, res)

format :: UnintKind -> [(String, [String], String)] -> [String]
format (UFun{}) eqns = fmtFun eqns
format (UArr{}) eqns = let fmt (f, as, r) = f ++ "[" ++ intercalate ", " as ++ "] = " ++ r in map fmt eqns

fmtFun :: [(String, [String], String)] -> [String]
fmtFun ls = map fmt ls
  where fmt (f, as, r) = f ++ " " ++ unwords (zipWith align as (lens ++ repeat 0)) ++ " = " ++ r
        lens           = map (maximum . (0:) . map length) $ transpose [as | (_, as, _) <- ls]
        align s i      = take (i `max` length s) (s ++ repeat ' ')

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.Optimize
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- SMT based optimization
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Tools.Optimize (OptimizeOpts(..), optimize, optimizeWith, minimize, minimizeWith, maximize, maximizeWith) where

import Data.Maybe (fromJust)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model (OrdSymbolic(..), EqSymbolic(..))
import Data.SBV.Provers.Prover   (satWith, defaultSMTCfg)
import Data.SBV.SMT.SMT          (SatModel, getModel, SMTConfig(..))
import Data.SBV.Utils.Boolean

-- | Optimizer configuration. Note that iterative and quantified approaches are in general not interchangeable.
-- For instance, iterative solutions will loop infinitely when there is no optimal value, but quantified solutions
-- can handle such problems. Of course, quantified problems are harder for SMT solvers, naturally.
data OptimizeOpts = Iterative  Bool   -- ^ Iteratively search. if True, it will be reporting progress
                  | Quantified        -- ^ Use quantifiers

-- | Symbolic optimization. Generalization on 'minimize' and 'maximize' that allows arbitrary
-- cost functions and comparisons.
optimizeWith :: (SatModel a, SymWord a, Show a, SymWord c, Show c)
             => SMTConfig                         -- ^ SMT configuration
             -> OptimizeOpts                      -- ^ Optimization options
             -> (SBV c -> SBV c -> SBool)         -- ^ comparator
             -> ([SBV a] -> SBV c)                -- ^ cost function
             -> Int                               -- ^ how many elements?
             -> ([SBV a] -> SBool)                -- ^ validity constraint
             -> IO (Maybe [a])
optimizeWith cfg (Iterative chatty) = iterOptimize chatty cfg
optimizeWith cfg Quantified         = quantOptimize cfg

-- | Variant of 'optimizeWith' using the default solver. See 'optimizeWith' for parameter descriptions.
optimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> (SBV c -> SBV c -> SBool) -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
optimize = optimizeWith defaultSMTCfg

-- | Variant of 'maximize' allowing the use of a user specified solver. See 'optimizeWith' for parameter descriptions.
maximizeWith :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => SMTConfig -> OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximizeWith cfg opts = optimizeWith cfg opts (.>=)

-- | Maximizes a cost function with respect to a constraint. Examples:
--
--   >>> maximize Quantified sum 3 (bAll (.< (10 :: SInteger)))
--   Just [9,9,9]
maximize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximize = maximizeWith defaultSMTCfg

-- | Variant of 'minimize' allowing the use of a user specified solver. See 'optimizeWith' for parameter descriptions.
minimizeWith :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => SMTConfig -> OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimizeWith cfg opts = optimizeWith cfg opts (.<=)

-- | Minimizes a cost function with respect to a constraint. Examples:
--
--   >>> minimize Quantified sum 3 (bAll (.> (10 :: SInteger)))
--   Just [11,11,11]
minimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimize = minimizeWith defaultSMTCfg

-- | Optimization using quantifiers
quantOptimize :: (SatModel a, SymWord a) => SMTConfig -> (SBV c -> SBV c -> SBool) -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
quantOptimize cfg cmp cost n valid = do
           m <- satWith cfg $ do xs <- mkExistVars  n
                                 ys <- mkForallVars n
                                 return $ valid xs &&& (valid ys ==> cost xs `cmp` cost ys)
           case getModel m of
              Right (True, _)  -> error "SBV: Backend solver reported \"unknown\""
              Right (False, a) -> return $ Just a
              Left _           -> return Nothing

-- | Optimization using iteration
iterOptimize :: (SatModel a, Show a, SymWord a, Show c, SymWord c) =>  Bool -> SMTConfig -> (SBV c -> SBV c -> SBool) -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
iterOptimize chatty cfg cmp cost n valid = do
        msg "Trying to find a satisfying solution."
        m <- satWith cfg $ valid `fmap` mkExistVars n
        case getModel m of
          Left _ -> do msg "No satisfying solutions found."
                       return Nothing
          Right (True, _)  -> error "SBV: Backend solver reported \"unknown\""
          Right (False, a) -> do msg $ "First solution found: " ++ show a
                                 let c = cost (map literal a)
                                 msg $ "Initial value is    : " ++ show (fromJust (unliteral c))
                                 msg "Starting iterative search."
                                 go (1::Int) a c
  where msg m | chatty = putStrLn $ "*** " ++ m
              | True   = return ()
        go i curSol curCost = do
                msg $ "Round " ++ show i ++ " ****************************"
                m <- satWith cfg $ do xs <- mkExistVars n
                                      return $ let c = cost xs in valid xs &&& (c `cmp` curCost &&& c ./= curCost)
                case getModel m of
                  Left _ -> do msg "The current solution is optimal. Terminating search."
                               return $ Just curSol
                  Right (True, _)  -> error "SBV: Backend solver reported \"unknown\""
                  Right (False, a) -> do msg $ "Solution: " ++ show a
                                         let c = cost (map literal a)
                                         msg $ "Value   : " ++ show (fromJust (unliteral c))
                                         go (i+1) a c

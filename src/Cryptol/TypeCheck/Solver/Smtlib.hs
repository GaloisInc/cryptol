-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE OverloadedStrings, RecordWildCards, PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cryptol.TypeCheck.Solver.Smtlib (simpDelayed) where

import           Cryptol.TypeCheck.AST as Cry
import           Cryptol.TypeCheck.Subst (fvs)
import           Cryptol.TypeCheck.InferTypes(Goal(..))
import           Cryptol.TypeCheck.Solver.FinOrd

import           SMTLib2      as SMT
import           SMTLib2.Int  as SMT
import           SMTLib2.Core as SMT
import qualified Control.Exception as X
import           Data.String(fromString)
import           Data.List(partition)
import           Data.Maybe(mapMaybe)
import qualified Data.Set as Set
import           System.Directory(findExecutable)
import           System.Environment(getExecutablePath)
import           System.FilePath((</>), takeDirectory)
import           System.Process(readProcessWithExitCode)
import           System.Exit(ExitCode(..))


simpDelayed :: [TParam] -> OrdFacts -> [Prop] -> [Goal] -> IO [Goal]
simpDelayed _qvars ordAsmp origAsmps goals =
  do ans <- mapM tryGoal goals

     let (_natsDone,natsNot) = partition snd ans
     -- XXX: check that `natsDone` also hold for the infinite case
     return (map fst natsNot)

  where
  vs = map toVar (Set.toList (fvs (ordFactsToProps ordAsmp,
                                        (origAsmps,map goal goals))))

  asmps = mapMaybe toPred (ordFactsToProps ordAsmp ++ origAsmps)

  tryGoal g = case toPred (goal g) of
                Just q -> do res <- cvc4 (toScript vs asmps q)
                             return (g, res == Unsat)
                              -- i.e., solved for Nats, anyway
                Nothing -> return (g, False)

toTerm :: Cry.Type -> Maybe SMT.Expr
toTerm ty =
  case ty of
    TCon tc ts  ->
      do es <- mapM toTerm ts
         case (tc, es) of
           (TC (TCNum x), [])  -> return (SMT.num x)

           (TF TCAdd, [e1,e2]) -> return (SMT.nAdd e1 e2)
           (TF TCSub, [e1,e2]) -> return (SMT.nSub e1 e2)
           (TF TCMul, [e1,e2]) -> return (SMT.nMul e1 e2)
           (TF TCDiv, [e1,e2]) -> return (SMT.nDiv e1 e2)
           (TF TCMod, [e1,e2]) -> return (SMT.nMod e1 e2)

           (TF TCMin, [e1,e2]) -> return (SMT.ite (SMT.nLeq e1 e2) e1 e2)
           (TF TCMax, [e1,e2]) -> return (SMT.ite (SMT.nLeq e1 e2) e2 e1)

           (TF TCLg2,   [_])   -> Nothing
           (TF TCExp,   [e1,e2])
               | Lit (LitNum x) <- e2
               , x >= 0        -> return $
                                  if x == 0
                                     then SMT.num (1 :: Int)
                                     else foldr1 SMT.nMul
                                        $ replicate (fromInteger x) e1
               | otherwise     -> Nothing

           (TF TCWidth, [_])   -> Nothing -- == lg2 (e + 1)

           (TF TCLenFromThen, _) -> Nothing
           (TF TCLenFromThenTo, _) -> Nothing

           _  -> Nothing


    Cry.TVar x      -> return (smtVar (toVar x))
    TUser _ _ t -> toTerm t
    TRec _      -> Nothing

toVar :: TVar -> SMT.Name
toVar (TVFree  x _ _ _) = fromString ("free"  ++ show x)
toVar (TVBound x _) = fromString ("bound" ++ show x)

smtVar :: SMT.Name -> SMT.Expr
smtVar x = app (I x []) []

toPred :: Cry.Prop -> Maybe SMT.Expr
toPred ty =
  case ty of
    TCon tc ts ->
      do es <- mapM toTerm ts
         case (tc,es) of
           (PC PEqual, [e1,e2])  -> return (e1 === e2)
           (PC PGeq, [e1,e2])    -> return (SMT.nLeq e2 e1)

           _                     -> Nothing

    Cry.TVar {} -> Nothing
    TUser _ _ t -> toPred t
    TRec {}     -> Nothing

toScript :: [SMT.Name] -> [SMT.Expr] -> SMT.Expr -> SMT.Script
toScript vs pes q =
  Script $
    [ SMT.CmdSetLogic "QF_LIA" ] ++
    [ SMT.CmdDeclareFun x [] SMT.tInt | x <- vs ] ++
    [ SMT.CmdAssert (SMT.nLeq (SMT.num (0::Int)) (smtVar x)) | x <- vs ] ++
    [ SMT.CmdAssert p | p <- pes ] ++
    [ SMT.CmdAssert (SMT.not q) ] ++
    [ SMT.CmdCheckSat ]

data SMTResult = Sat | Unsat | Unknown
                  deriving (Eq,Show)

-- | First look for @cvc4@ in the path, but failing that, assume that it's 
-- installed side-by-side with Cryptol.
findCvc4 :: IO FilePath
findCvc4 = do
  mfp <- findExecutable "cvc4"
  case mfp of
    Just fp -> return fp
    Nothing -> do
     bindir <- takeDirectory `fmap` getExecutablePath
     return (bindir </> "cvc4")

cvc4 :: SMT.Script -> IO SMTResult
cvc4 script =
  X.handle (\(_::X.IOException) -> return Unknown) $
  do let txt = show (SMT.pp script)
     cvc4path <- findCvc4
     (ex,out,err) <- readProcessWithExitCode cvc4path ["--lang=smtlib2","--rewrite-divk","-"] txt
     case ex of
       ExitFailure 10  -> return Sat
       ExitFailure 20  -> return Unsat
       ExitFailure 127 -> return Unknown -- cvc4 program not found
       ExitSuccess
         | out == "sat\n"     -> return Sat
         | out == "unsat\n"   -> return Unsat
         | out == "unknwon\n" -> return Unknown

       -- XXX: We should not print to STDOUT here.
       -- Report to a separate logger.
       x -> do putStrLn "Called to CVC4 failed!!!"
               putStrLn ("Exit code: " ++ show x)
               putStrLn "Script"
               putStrLn txt

               putStrLn "Standard out:"
               putStrLn out

               putStrLn "Standard error:"
               putStrLn err

               return Unknown -- or error



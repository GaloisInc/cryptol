-- |
-- Module      :  Cryptol.Symbolic
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Symbolic
 ( ProverCommand(..)
 , QueryType(..)
 , SatNum(..)
 , ProverResult(..)
 , ProverStats
 , CounterExampleType(..)
   -- * FinType
 , FinType(..)
 , finType
 , unFinType
 , predArgTypes
 ) where


import Data.IORef(IORef)


import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.TypeCheck.AST
import           Cryptol.Eval.Type (TValue(..), evalType)
import           Cryptol.Utils.Ident (Ident)
import           Cryptol.Utils.RecordMap
import           Cryptol.Utils.PP

import Prelude ()
import Prelude.Compat
import Data.Time (NominalDiffTime)

type SatResult = [(Type, Expr, Concrete.Value)]

data SatNum = AllSat | SomeSat Int
  deriving (Show)

data QueryType = SatQuery SatNum | ProveQuery | SafetyQuery
  deriving (Show)

data ProverCommand = ProverCommand {
    pcQueryType :: QueryType
    -- ^ The type of query to run
  , pcProverName :: String
    -- ^ Which prover to use (one of the strings in 'proverConfigs')
  , pcVerbose :: Bool
    -- ^ Verbosity flag passed to SBV
  , pcValidate :: Bool
    -- ^ Model validation flag passed to SBV
  , pcProverStats :: !(IORef ProverStats)
    -- ^ Record timing information here
  , pcExtraDecls :: [DeclGroup]
    -- ^ Extra declarations to bring into scope for symbolic
    -- simulation
  , pcSmtFile :: Maybe FilePath
    -- ^ Optionally output the SMTLIB query to a file
  , pcExpr :: Expr
    -- ^ The typechecked expression to evaluate
  , pcSchema :: Schema
    -- ^ The 'Schema' of @pcExpr@
  , pcIgnoreSafety :: Bool
    -- ^ Should we ignore safety predicates?
  }

type ProverStats = NominalDiffTime

-- | A @:prove@ command can fail either because some
--   input causes the predicate to violate a safety assertion,
--   or because the predicate returns false for some input.
data CounterExampleType = SafetyViolation | PredicateFalsified

-- | A prover result is either an error message, an empty result (eg
-- for the offline prover), a counterexample or a lazy list of
-- satisfying assignments.
data ProverResult = AllSatResult [SatResult] -- LAZY
                  | ThmResult    [Type]
                  | CounterExample CounterExampleType SatResult
                  | EmptyResult
                  | ProverError  String



predArgTypes :: QueryType -> Schema -> Either String [FinType]
predArgTypes qtype schema@(Forall ts ps ty)
  | null ts && null ps =
      case go <$> (evalType mempty ty) of
        Right (Just fts) -> Right fts
        _ | SafetyQuery <- qtype -> Left $ "Expected finite result type:\n" ++ show (pp schema)
          | otherwise -> Left $ "Not a valid predicate type:\n" ++ show (pp schema)
  | otherwise = Left $ "Not a monomorphic type:\n" ++ show (pp schema)
  where
    go :: TValue -> Maybe [FinType]
    go TVBit             = Just []
    go (TVFun ty1 ty2)   = (:) <$> finType ty1 <*> go ty2
    go tv
      | Just _ <- finType tv
      , SafetyQuery <- qtype
      = Just []

      | otherwise
      = Nothing

data FinType
    = FTBit
    | FTInteger
    | FTIntMod Integer
    | FTRational
    | FTFloat Integer Integer
    | FTSeq Int FinType  -- TODO! Int -> Integer
    | FTTuple [FinType]
    | FTRecord (RecordMap Ident FinType)

numType :: Integer -> Maybe Int
numType n
  | 0 <= n && n <= toInteger (maxBound :: Int) = Just (fromInteger n)
  | otherwise = Nothing

finType :: TValue -> Maybe FinType
finType ty =
  case ty of
    TVBit            -> Just FTBit
    TVInteger        -> Just FTInteger
    TVIntMod n       -> Just (FTIntMod n)
    TVRational       -> Just FTRational
    TVFloat e p      -> Just (FTFloat e p)
    TVSeq n t        -> FTSeq <$> numType n <*> finType t
    TVTuple ts       -> FTTuple <$> traverse finType ts
    TVRec fields     -> FTRecord <$> traverse finType fields
    TVAbstract {}    -> Nothing
    _                     -> Nothing

unFinType :: FinType -> Type
unFinType fty =
  case fty of
    FTBit        -> tBit
    FTInteger    -> tInteger
    FTIntMod n   -> tIntMod (tNum n)
    FTRational   -> tRational
    FTFloat e p  -> tFloat (tNum e) (tNum p)
    FTSeq l ety  -> tSeq (tNum l) (unFinType ety)
    FTTuple ftys -> tTuple (unFinType <$> ftys)
    FTRecord fs  -> tRec (unFinType <$> fs)

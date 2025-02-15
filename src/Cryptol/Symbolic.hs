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
{-# LANGUAGE OverloadedStrings #-}
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
 , FinNominalType(..)
 , finType
 , unFinType
 , predArgTypes
   -- * VarShape
 , VarShape(..)
 , varShapeToValue
 , freshVar
 , computeModel
 , FreshVarFns(..)
 , modelPred
 , varModelPred
 , varToExpr
 , flattenShape
 , flattenShapes
 ) where


import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IntMap
import Data.IORef(IORef)
import Data.List (genericReplicate)
import Data.Ratio
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import qualified LibBF as FP


import           Cryptol.Backend
import           Cryptol.Backend.FloatHelpers(bfValue)
import           Cryptol.Backend.WordValue (wordVal)

import qualified Cryptol.Eval.Concrete as Concrete
import           Cryptol.Eval.Value
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.Eval.Type
  (TValue(..), TNominalTypeValue(..), evalType,tValTy,tNumValTy,ConInfo(..))
import           Cryptol.Utils.Ident (Ident,prelPrim,floatPrim)
import           Cryptol.Utils.RecordMap
import           Cryptol.Utils.Panic
import           Cryptol.Utils.PP


import Prelude ()
import Prelude.Compat
import Data.Time (NominalDiffTime)

type SatResult = [(TValue, Expr, Concrete.Value)]

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
                  | ThmResult    [TValue]
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
    | FTSeq Integer FinType
    | FTTuple [FinType]
    | FTRecord (RecordMap Ident FinType)
    | FTNominal NominalType [Either Nat' TValue] FinNominalType

data FinNominalType =
    FStruct (RecordMap Ident FinType)
  | FEnum (Vector (ConInfo FinType))

finType :: TValue -> Maybe FinType
finType ty =
  case ty of
    TVBit               -> Just FTBit
    TVInteger           -> Just FTInteger
    TVIntMod n          -> Just (FTIntMod n)
    TVRational          -> Just FTRational
    TVFloat e p         -> Just (FTFloat e p)
    TVSeq n t           -> FTSeq n <$> finType t
    TVTuple ts          -> FTTuple <$> traverse finType ts
    TVRec fields        -> FTRecord <$> traverse finType fields
    TVNominal u ts nv   -> FTNominal u ts <$>
      case nv of
        TVStruct body -> FStruct <$> traverse finType body
        TVEnum cs     -> FEnum   <$> traverse (traverse finType) cs
        TVAbstract    -> Nothing

    TVArray{}           -> Nothing
    TVStream{}          -> Nothing
    TVFun{}             -> Nothing

finTypeToType :: FinType -> Type
finTypeToType fty =
  case fty of
    FTBit             -> tBit
    FTInteger         -> tInteger
    FTIntMod n        -> tIntMod (tNum n)
    FTRational        -> tRational
    FTFloat e p       -> tFloat (tNum e) (tNum p)
    FTSeq l ety       -> tSeq (tNum l) (finTypeToType ety)
    FTTuple ftys      -> tTuple (finTypeToType <$> ftys)
    FTRecord fs       -> tRec (finTypeToType <$> fs)
    FTNominal u ts _  -> tNominal u (map unArg ts)
 where
  unArg (Left Inf)     = tInf
  unArg (Left (Nat n)) = tNum n
  unArg (Right t)      = tValTy t

unFinType :: FinType -> TValue
unFinType fty =
  case fty of
    FTBit             -> TVBit
    FTInteger         -> TVInteger
    FTIntMod n        -> TVIntMod n
    FTRational        -> TVRational
    FTFloat e p       -> TVFloat e p
    FTSeq n ety       -> TVSeq n (unFinType ety)
    FTTuple ftys      -> TVTuple (unFinType <$> ftys)
    FTRecord fs       -> TVRec   (unFinType <$> fs)

    FTNominal u ts nv -> TVNominal u ts $
       case nv of
          FStruct fs  -> TVStruct (unFinType <$> fs)
          FEnum cs    -> TVEnum (fmap unFinType <$> cs)

data VarShape sym
  = VarBit (SBit sym)
  | VarInteger (SInteger sym)
  | VarRational (SInteger sym) (SInteger sym)
  | VarFloat (SFloat sym)
  | VarWord (SWord sym)
  | VarFinSeq Integer [VarShape sym]
  | VarTuple [VarShape sym]
  | VarRecord (RecordMap Ident (VarShape sym))
  | VarEnum (SInteger sym) (Vector (ConInfo (VarShape sym)))

ppVarShape :: Backend sym => sym -> VarShape sym -> Doc
ppVarShape _sym (VarBit _b) = text "<bit>"
ppVarShape _sym (VarInteger _i) = text "<integer>"
ppVarShape _sym (VarFloat _f) = text "<float>"
ppVarShape _sym (VarRational _n _d) = text "<rational>"
ppVarShape sym (VarWord w) = text "<word:" <> integer (wordLen sym w) <> text ">"
ppVarShape sym (VarFinSeq _ xs) =
  ppList (map (ppVarShape sym) xs)
ppVarShape sym (VarTuple xs) =
  ppTuple (map (ppVarShape sym) xs)
ppVarShape sym (VarRecord fs) =
  ppRecord (map ppField (displayFields fs))
 where
  ppField (f,v) = pp f <+> char '=' <+> ppVarShape sym v
ppVarShape _sym (VarEnum {}) = text "<enum>"


-- | Flatten structured shapes (like tuples and sequences), leaving only
--   a sequence of variable shapes of base type.
flattenShapes :: [VarShape sym] -> [VarShape sym] -> [VarShape sym]
flattenShapes []     tl = tl
flattenShapes (x:xs) tl = flattenShape x (flattenShapes xs tl)

flattenShape :: VarShape sym -> [VarShape sym] -> [VarShape sym]
flattenShape x tl =
  case x of
    VarBit{}       -> x : tl
    VarInteger{}   -> x : tl
    VarRational{}  -> x : tl
    VarWord{}      -> x : tl
    VarFloat{}     -> x : tl
    VarFinSeq _ vs -> flattenShapes vs tl
    VarTuple vs    -> flattenShapes vs tl
    VarRecord fs   -> flattenShapes (recordElements fs) tl
    VarEnum _ cs   -> x : flattenShapes allCons tl
      where
      allCons = concatMap (Vector.toList . conFields) (Vector.toList cs)

varShapeToValue :: Backend sym => sym -> VarShape sym -> GenValue sym
varShapeToValue sym var =
  case var of
    VarBit b     -> VBit b
    VarInteger i -> VInteger i
    VarRational n d -> VRational (SRational n d)
    VarWord w    -> VWord (wordVal w)
    VarFloat f   -> VFloat f
    VarFinSeq n vs -> mkFinSeq sym n (map (varShapeToValue sym) vs)
    VarTuple vs  -> VTuple (map (pure . varShapeToValue sym) vs)
    VarRecord fs -> VRecord (fmap (pure . varShapeToValue sym) fs)
    VarEnum tag cons ->
      VEnum tag (IntMap.fromList
                   (zip [ 0 .. ] [ pure . varShapeToValue sym <$> c
                                 | c <- Vector.toList cons ]))

data FreshVarFns sym =
  FreshVarFns
  { freshBitVar     :: IO (SBit sym)
  , freshWordVar    :: Integer -> IO (SWord sym)
  , freshIntegerVar :: Maybe Integer -> Maybe Integer -> IO (SInteger sym)
  , freshFloatVar   :: Integer -> Integer -> IO (SFloat sym)
  }

freshVar :: Backend sym => FreshVarFns sym -> FinType -> IO (VarShape sym)
freshVar fns tp =
  case tp of
    FTBit         -> VarBit      <$> freshBitVar fns
    FTInteger     -> VarInteger  <$> freshIntegerVar fns Nothing Nothing
    FTRational    -> VarRational
                        <$> freshIntegerVar fns Nothing Nothing
                        <*> freshIntegerVar fns (Just 1) Nothing
    FTIntMod 0    -> panic "freshVariable" ["0 modulus not allowed"]
    FTIntMod m    -> VarInteger  <$> freshIntegerVar fns (Just 0) (Just (m-1))
    FTFloat e p   -> VarFloat    <$> freshFloatVar fns e p
    FTSeq n FTBit -> VarWord     <$> freshWordVar fns (toInteger n)
    FTSeq n t     -> VarFinSeq (toInteger n) <$> sequence (genericReplicate n (freshVar fns t))
    FTTuple ts    -> VarTuple    <$> mapM (freshVar fns) ts
    FTRecord fs   -> VarRecord   <$> traverse (freshVar fns) fs
    FTNominal _ _ nv ->
      case nv of
        FStruct fs -> VarRecord <$> traverse (freshVar fns) fs
        FEnum conTs ->
          do let maxCon = toInteger (Vector.length conTs - 1)
             tag <- freshIntegerVar fns (Just 0) (Just maxCon)
             cons <- traverse (traverse (freshVar fns)) conTs
             pure (VarEnum tag cons)


computeModel ::
  PrimMap ->
  [FinType] ->
  [VarShape Concrete.Concrete] ->
  [(TValue, Expr, Concrete.Value)]
computeModel _ [] [] = []
computeModel primMap (t:ts) (v:vs) =
  do let v' = varShapeToValue Concrete.Concrete v
     let t' = unFinType t
     let e  = varToExpr primMap t v
     let zs = computeModel primMap ts vs
      in ((t',e,v'):zs)
computeModel _ _ _ = panic "computeModel" ["type/value list mismatch"]



modelPred  ::
  Backend sym =>
  sym ->
  [VarShape sym] ->
  [VarShape Concrete.Concrete] ->
  SEval sym (SBit sym)
modelPred sym vs xs =
  do ps <- mapM (varModelPred sym) (zip vs xs)
     foldM (bitAnd sym) (bitLit sym True) ps

varModelPred ::
  Backend sym =>
  sym ->
  (VarShape sym, VarShape Concrete.Concrete) ->
  SEval sym (SBit sym)
varModelPred sym vx =
  case vx of
    (VarBit b, VarBit blit) ->
      bitEq sym b (bitLit sym blit)

    (VarInteger i, VarInteger ilit) ->
      intEq sym i =<< integerLit sym ilit

    (VarRational n d, VarRational nlit dlit) ->
      do n' <- integerLit sym nlit
         d' <- integerLit sym dlit
         rationalEq sym (SRational n d) (SRational n' d')

    (VarWord w, VarWord (Concrete.BV len wlit)) ->
      wordEq sym w =<< wordLit sym len wlit

    (VarFloat f, VarFloat flit) ->
      fpLogicalEq sym f =<< fpExactLit sym flit

    (VarFinSeq _n vs, VarFinSeq _ xs) -> modelPred sym vs xs
    (VarTuple vs, VarTuple xs) -> modelPred sym vs xs
    (VarRecord vs, VarRecord xs) -> modelPred sym (recordElements vs) (recordElements xs)
    (VarEnum vi vcons,  VarEnum i cons) ->
      do tag     <- integerLit sym i
         sameTag <- intEq sym tag vi
         let i' = fromInteger i
             flds = Vector.toList . conFields
         sameFs  <- case (vcons Vector.!? i', cons Vector.!? i') of
                      (Just con1, Just con2) ->
                         modelPred sym (flds con1) (flds con2)
                      _ -> panic "varModelPred" ["malformed constructor"]
         bitAnd sym sameTag sameFs

    _ -> panic "varModelPred" ["variable shape mismatch!"]


varToExpr :: PrimMap -> FinType -> VarShape Concrete.Concrete -> Expr
varToExpr prims = go
  where

  prim n = ePrim prims (prelPrim n)

  go :: FinType -> VarShape Concrete.Concrete -> Expr
  go ty val =
    case (ty,val) of
      (FTNominal nt ts (FStruct tfs), VarRecord vfs) ->
        let res = zipRecords (\_lbl v t -> go t v) vfs tfs
         in case res of
              Left _ -> mismatch -- different fields
              Right efs ->
                let con = case ntDef nt of
                            Struct c -> ntConName c
                            Enum {} -> panic "varToExpr" ["Enum, expected Struct"]
                            Abstract {} -> panic "varToExpr"
                              ["Abstract, expected Struct"]
                    f = foldl (\x t -> ETApp x (tNumValTy t)) (EVar con) ts
                 in EApp f (ERec efs)

      (FTNominal nt ts (FEnum cons), VarEnum tag conVs) ->
         foldl EApp conName args
         where
         tag' = fromInteger tag
         args = case (cons Vector.!? tag', conVs Vector.!? tag') of
                 (Just conT, Just conV) ->
                    Vector.toList
                       (Vector.zipWith go (conFields conT) (conFields conV))
                 _ -> panic "varToExpr" ["Malformed constructor"]

         conName =
           case ntDef nt of
             Enum cs | c : _ <- filter ((tag' ==) . ecNumber ) cs ->
                foldl (\x t -> ETApp x (tNumValTy t)) (EVar (ecName c)) ts

             _ -> panic "varToExpr" ["Missing constructor"]

      (FTRecord tfs, VarRecord vfs) ->
        let res = zipRecords (\_lbl v t -> go t v) vfs tfs
         in case res of
              Left _ -> mismatch -- different fields
              Right efs -> ERec efs
      (FTTuple ts, VarTuple tvs) ->
        ETuple (zipWith go ts tvs)

      (FTBit, VarBit b) ->
        prim (if b then "True" else "False")

      (FTInteger, VarInteger i) ->
        -- This works uniformly for values of type Integer or Z n
        ETApp (ETApp (prim "number") (tNum i)) (finTypeToType ty)

      (FTIntMod _, VarInteger i) ->
        -- This works uniformly for values of type Integer or Z n
        ETApp (ETApp (prim "number") (tNum i)) (finTypeToType ty)

      (FTRational, VarRational n d) ->
        let n' = ETApp (ETApp (prim "number") (tNum n)) tInteger
            d' = ETApp (ETApp (prim "number") (tNum d)) tInteger
         in EApp (EApp (prim "ratio") n') d'

      (FTFloat e p, VarFloat f) ->
        floatToExpr prims e p (bfValue f)

      (FTSeq _ FTBit, VarWord (Concrete.BV _ v)) ->
        ETApp (ETApp (prim "number") (tNum v)) (finTypeToType ty)

      (FTSeq _ t, VarFinSeq _ svs) ->
        EList (map (go t) svs) (finTypeToType t)

      _ -> mismatch
    where
      mismatch =
           panic "Cryptol.Symbolic.varToExpr"
             ["type mismatch:"
             , show (pp (finTypeToType ty))
             , show (ppVarShape Concrete.Concrete val)
             ]

floatToExpr :: PrimMap -> Integer -> Integer -> FP.BigFloat -> Expr
floatToExpr prims e p f =
  case FP.bfToRep f of
    FP.BFNaN -> mkP "fpNaN"
    FP.BFRep sign num ->
      case (sign,num) of
        (FP.Pos, FP.Zero)   -> mkP "fpPosZero"
        (FP.Neg, FP.Zero)   -> mkP "fpNegZero"
        (FP.Pos, FP.Inf)    -> mkP "fpPosInf"
        (FP.Neg, FP.Inf)    -> mkP "fpNegInf"
        (_, FP.Num m ex) ->
            let r = toRational m * (2 ^^ ex)
            in EProofApp $ ePrim prims (prelPrim "fraction")
                          `ETApp` tNum (numerator r)
                          `ETApp` tNum (denominator r)
                          `ETApp` tNum (0 :: Int)
                          `ETApp` tFloat (tNum e) (tNum p)
  where
  mkP n = EProofApp $ ePrim prims (floatPrim n) `ETApp` (tNum e) `ETApp` (tNum p)

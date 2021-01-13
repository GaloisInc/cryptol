-- |
-- Module      :  Cryptol.Eval.Type
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Eval.Type where

import Cryptol.Backend.Monad (evalPanic)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.PP(pp)
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.RecordMap

import Data.Maybe(fromMaybe)
import qualified Data.IntMap.Strict as IntMap
import GHC.Generics (Generic)
import Control.DeepSeq

-- | An evaluated type of kind *.
-- These types do not contain type variables, type synonyms, or type functions.
data TValue
  = TVBit                     -- ^ @ Bit @
  | TVInteger                 -- ^ @ Integer @
  | TVFloat Integer Integer   -- ^ @ Float e p @
  | TVIntMod Integer          -- ^ @ Z n @
  | TVRational                -- ^ @ Rational @
  | TVGen TValue              -- ^ @ Gen a @
  | TVArray TValue TValue     -- ^ @ Array a b @
  | TVSeq Integer TValue      -- ^ @ [n]a @
  | TVStream TValue           -- ^ @ [inf]t @
  | TVTuple [TValue]          -- ^ @ (a, b, c )@
  | TVRec (RecordMap Ident TValue) -- ^ @ { x : a, y : b, z : c } @
  | TVFun TValue TValue       -- ^ @ a -> b @
  | TVNewtype Newtype
              [Either Nat' TValue]
              (RecordMap Ident TValue)     -- ^ a named newtype
  | TVAbstract UserTC [Either Nat' TValue] -- ^ an abstract type
    deriving (Generic, NFData, Eq)

-- | Convert a type value back into a regular type
tValTy :: TValue -> Type
tValTy tv =
  case tv of
    TVBit       -> tBit
    TVInteger   -> tInteger
    TVFloat e p -> tFloat (tNum e) (tNum p)
    TVIntMod n  -> tIntMod (tNum n)
    TVRational  -> tRational
    TVGen a     -> tGen (tValTy a)
    TVArray a b -> tArray (tValTy a) (tValTy b)
    TVSeq n t   -> tSeq (tNum n) (tValTy t)
    TVStream t  -> tSeq tInf (tValTy t)
    TVTuple ts  -> tTuple (map tValTy ts)
    TVRec fs    -> tRec (fmap tValTy fs)
    TVFun t1 t2 -> tFun (tValTy t1) (tValTy t2)
    TVNewtype nt vs _ -> tNewtype nt (map tNumValTy vs)
    TVAbstract u vs -> tAbstract u (map tNumValTy vs)

tNumTy :: Nat' -> Type
tNumTy Inf     = tInf
tNumTy (Nat n) = tNum n

tNumValTy :: Either Nat' TValue -> Type
tNumValTy = either tNumTy tValTy


instance Show TValue where
  showsPrec p v = showsPrec p (tValTy v)


-- Utilities -------------------------------------------------------------------

-- | True if the evaluated value is @Bit@
isTBit :: TValue -> Bool
isTBit TVBit = True
isTBit _ = False

-- | Produce a sequence type value
tvSeq :: Nat' -> TValue -> TValue
tvSeq (Nat n) t = TVSeq n t
tvSeq Inf     t = TVStream t

-- | Coerce an extended natural into an integer,
--   for values known to be finite
finNat' :: Nat' -> Integer
finNat' n' =
  case n' of
    Nat x -> x
    Inf   -> panic "Cryptol.Eval.Value.finNat'" [ "Unexpected `inf`" ]


-- Type Evaluation -------------------------------------------------------------

newtype TypeEnv =
  TypeEnv
  { envTypeMap  :: IntMap.IntMap (Either Nat' TValue) }

instance Monoid TypeEnv where
  mempty = TypeEnv mempty

instance Semigroup TypeEnv where
  l <> r = TypeEnv
    { envTypeMap  = IntMap.union (envTypeMap l) (envTypeMap r) }

lookupTypeVar :: TVar -> TypeEnv -> Maybe (Either Nat' TValue)
lookupTypeVar tv env = IntMap.lookup (tvUnique tv) (envTypeMap env)

bindTypeVar :: TVar -> Either Nat' TValue -> TypeEnv -> TypeEnv
bindTypeVar tv ty env = env{ envTypeMap = IntMap.insert (tvUnique tv) ty (envTypeMap env) }

-- | Evaluation for types (kind * or #).
evalType :: TypeEnv -> Type -> Either Nat' TValue
evalType env ty =
  case ty of
    TVar tv ->
      case lookupTypeVar tv env of
        Just v -> v
        Nothing -> evalPanic "evalType" ["type variable not bound", show tv]

    TUser _ _ ty'  -> evalType env ty'
    TRec fields    -> Right $ TVRec (fmap val fields)

    TNewtype nt ts -> Right $ TVNewtype nt tvs $ evalNewtypeBody env nt tvs
        where tvs = map (evalType env) ts

    TCon (TC c) ts ->
      case (c, ts) of
        (TCBit, [])     -> Right $ TVBit
        (TCInteger, []) -> Right $ TVInteger
        (TCRational, []) -> Right $ TVRational
        (TCGen, [a])     -> Right $ TVGen (val a)
        (TCFloat, [e,p])-> Right $ TVFloat (inum e) (inum p)
        (TCIntMod, [n]) -> case num n of
                             Inf   -> evalPanic "evalType" ["invalid type Z inf"]
                             Nat m -> Right $ TVIntMod m
        (TCArray, [a, b]) -> Right $ TVArray (val a) (val b)
        (TCSeq, [n, t]) -> Right $ tvSeq (num n) (val t)
        (TCFun, [a, b]) -> Right $ TVFun (val a) (val b)
        (TCTuple _, _)  -> Right $ TVTuple (map val ts)
        (TCNum n, [])   -> Left $ Nat n
        (TCInf, [])     -> Left $ Inf
        (TCAbstract u,vs) ->
            case kindOf ty of
              KType -> Right $ TVAbstract u (map (evalType env) vs)
              k -> evalPanic "evalType"
                [ "Unsupported"
                , "*** Abstract type of kind: " ++ show (pp k)
                , "*** Name: " ++ show (pp u)
                ]

        _ -> evalPanic "evalType" ["not a value type", show ty]
    TCon (TF f) ts      -> Left $ evalTF f (map num ts)
    TCon (PC p) _       -> evalPanic "evalType" ["invalid predicate symbol", show p]
    TCon (TError _) ts -> evalPanic "evalType"
                             $ "Lingering invalid type" : map (show . pp) ts
  where
    val = evalValType env
    num = evalNumType env
    inum x = case num x of
               Nat i -> i
               Inf   -> evalPanic "evalType"
                                  ["Expecting a finite size, but got `inf`"]

-- | Evaluate the body of a newtype, given evaluated arguments
evalNewtypeBody :: TypeEnv -> Newtype -> [Either Nat' TValue] -> RecordMap Ident TValue
evalNewtypeBody env0 nt args = fmap (evalValType env') (ntFields nt)
  where
  env' = loop env0 (ntParams nt) args

  loop env [] [] = env
  loop env (p:ps) (a:as) = loop (bindTypeVar (TVBound p) a env) ps as
  loop _ _ _ = evalPanic "evalNewtype" ["type parameter/argument mismatch"]

-- | Evaluation for value types (kind *).
evalValType :: TypeEnv -> Type -> TValue
evalValType env ty =
  case evalType env ty of
    Left _ -> evalPanic "evalValType" ["expected value type, found numeric type"]
    Right t -> t

-- | Evaluation for number types (kind #).
evalNumType :: TypeEnv -> Type -> Nat'
evalNumType env ty =
  case evalType env ty of
    Left n -> n
    Right _ -> evalPanic "evalValType" ["expected numeric type, found value type"]


-- | Reduce type functions, raising an exception for undefined values.
evalTF :: TFun -> [Nat'] -> Nat'
evalTF f vs
  | TCAdd           <- f, [x,y]   <- vs  =      nAdd x y
  | TCSub           <- f, [x,y]   <- vs  = mb $ nSub x y
  | TCMul           <- f, [x,y]   <- vs  =      nMul x y
  | TCDiv           <- f, [x,y]   <- vs  = mb $ nDiv x y
  | TCMod           <- f, [x,y]   <- vs  = mb $ nMod x y
  | TCWidth         <- f, [x]     <- vs  =      nWidth x
  | TCExp           <- f, [x,y]   <- vs  =      nExp x y
  | TCMin           <- f, [x,y]   <- vs  =      nMin x y
  | TCMax           <- f, [x,y]   <- vs  =      nMax x y
  | TCCeilDiv       <- f, [x,y]   <- vs  = mb $ nCeilDiv x y
  | TCCeilMod       <- f, [x,y]   <- vs  = mb $ nCeilMod x y
  | TCLenFromThenTo <- f, [x,y,z] <- vs  = mb $ nLenFromThenTo x y z
  | otherwise  = evalPanic "evalTF"
                        ["Unexpected type function:", show ty]

  where mb = fromMaybe (evalPanic "evalTF" ["type cannot be demoted", show (pp ty)])
        ty = TCon (TF f) (map tNat' vs)

-- |
-- Module      :  Cryptol.TypeCheck.TypeOf
-- Copyright   :  (c) 2014-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe                                #-}
{-# LANGUAGE ViewPatterns                        #-}
{-# LANGUAGE PatternGuards                       #-}
module Cryptol.TypeCheck.TypeOf
  ( fastTypeOf
  , fastSchemaOf
  ) where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst
import Cryptol.Utils.Panic
import Cryptol.Utils.PP

import           Data.Map    (Map)
import qualified Data.Map as Map

-- | Given a typing environment and an expression, compute the type of
-- the expression as quickly as possible, assuming that the expression
-- is well formed with correct type annotations.
fastTypeOf :: Map Name Schema -> Expr -> Type
fastTypeOf tyenv expr =
  case expr of
    -- Monomorphic fragment
    EList es t    -> tSeq (tNum (length es)) t
    ETuple es     -> tTuple (map (fastTypeOf tyenv) es)
    ERec fields   -> tRec [ (name, fastTypeOf tyenv e) | (name, e) <- fields ]
    ESel e sel    -> typeSelect (fastTypeOf tyenv e) sel
    ESet e _ _    -> fastTypeOf tyenv e
    EIf _ e _     -> fastTypeOf tyenv e
    EComp len t _ _ -> tSeq len t
    EAbs x t e    -> tFun t (fastTypeOf (Map.insert x (Forall [] [] t) tyenv) e)
    EApp e _      -> case tIsFun (fastTypeOf tyenv e) of
                        Just (_, t) -> t
                        Nothing     -> panic "Cryptol.TypeCheck.TypeOf.fastTypeOf"
                                         [ "EApp with non-function operator" ]
    -- Polymorphic fragment
    EVar      {}  -> polymorphic
    ETAbs     {}  -> polymorphic
    ETApp     {}  -> polymorphic
    EProofAbs {}  -> polymorphic
    EProofApp {}  -> polymorphic
    EWhere    {}  -> polymorphic
  where
    polymorphic =
      case fastSchemaOf tyenv expr of
        Forall [] [] ty -> ty
        _ -> panic "Cryptol.TypeCheck.TypeOf.fastTypeOf"
               [ "unexpected polymorphic type" ]

fastSchemaOf :: Map Name Schema -> Expr -> Schema
fastSchemaOf tyenv expr =
  case expr of
    -- Polymorphic fragment
    EVar x         -> case Map.lookup x tyenv of
                         Just ty -> ty
                         Nothing -> panic "Cryptol.TypeCheck.TypeOf.fastSchemaOf"
                               [ "EVar failed to find type variable:", show x ]
    ETAbs tparam e -> case fastSchemaOf tyenv e of
                        Forall tparams props ty -> Forall (tparam : tparams) props ty
    ETApp e t      -> case fastSchemaOf tyenv e of
                        Forall (tparam : tparams) props ty
                          -> Forall tparams (map (plainSubst s) props) (plainSubst s ty)
                          where s = singleSubst (tpVar tparam) t
                        _ -> panic "Cryptol.TypeCheck.TypeOf.fastSchemaOf"
                               [ "ETApp body with no type parameters" ]
                        -- When calling 'fastSchemaOf' on a
                        -- polymorphic function with instantiated type
                        -- variables but undischarged type
                        -- constraints, we would prefer to see the
                        -- instantiated constraints in an
                        -- un-simplified form. Thus we use
                        -- 'plainSubst' instead of 'apSubst' on the
                        -- type constraints.
    EProofAbs p e  -> case fastSchemaOf tyenv e of
                        Forall [] props ty -> Forall [] (p : props) ty
                        _ -> panic "Cryptol.TypeCheck.TypeOf.fastSchemaOf"
                               [ "EProofAbs with polymorphic expression" ]
    EProofApp e    -> case fastSchemaOf tyenv e of
                        Forall [] (_ : props) ty -> Forall [] props ty
                        _ -> panic "Cryptol.TypeCheck.TypeOf.fastSchemaOf"
                               [ "EProofApp with polymorphic expression or"
                               , "no props in scope"
                               ]
    EWhere e dgs   -> fastSchemaOf (foldr addDeclGroup tyenv dgs) e
                        where addDeclGroup (Recursive ds) = flip (foldr addDecl) ds
                              addDeclGroup (NonRecursive d) = addDecl d
                              addDecl d = Map.insert (dName d) (dSignature d)
    -- Monomorphic fragment
    EList  {}      -> monomorphic
    ETuple {}      -> monomorphic
    ERec   {}      -> monomorphic
    ESet   {}      -> monomorphic
    ESel   {}      -> monomorphic
    EIf    {}      -> monomorphic
    EComp  {}      -> monomorphic
    EApp   {}      -> monomorphic
    EAbs   {}      -> monomorphic
  where
    monomorphic = Forall [] [] (fastTypeOf tyenv expr)

-- | Apply a substitution to a type *without* simplifying
-- constraints like @Arith [n]a@ to @Arith a@. (This is in contrast to
-- 'apSubst', which performs simplifications wherever possible.)
plainSubst :: Subst -> Type -> Type
plainSubst s ty =
  case ty of
    TCon tc ts   -> TCon tc (map (plainSubst s) ts)
    TUser f ts t -> TUser f (map (plainSubst s) ts) (plainSubst s t)
    TRec fs      -> TRec [ (x, plainSubst s t) | (x, t) <- fs ]
    TVar x       -> apSubst s (TVar x)

-- | Yields the return type of the selector on the given argument type.
typeSelect :: Type -> Selector -> Type
typeSelect (TUser _ _ ty) sel = typeSelect ty sel
typeSelect (tIsTuple -> Just ts) (TupleSel i _)
  | i < length ts = ts !! i
typeSelect (TRec fields) (RecordSel n _)
  | Just ty <- lookup n fields = ty
typeSelect (tIsSeq -> Just (_, a)) ListSel{} = a
typeSelect (tIsSeq -> Just (n, a)) sel@TupleSel{} = tSeq n (typeSelect a sel)
typeSelect (tIsSeq -> Just (n, a)) sel@RecordSel{} = tSeq n (typeSelect a sel)
typeSelect ty _ = panic "Cryptol.TypeCheck.TypeOf.typeSelect"
                    [ "cannot apply selector to value of type", render (pp ty) ]

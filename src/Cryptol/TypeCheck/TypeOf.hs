-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe                                #-}
{-# LANGUAGE ViewPatterns                        #-}
module Cryptol.TypeCheck.TypeOf
  ( fastTypeOf
  , fastSchemaOf
  ) where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst
import Cryptol.Prims.Types (typeOf)
import Cryptol.Utils.Panic
import Cryptol.Utils.PP

import           Data.Map    (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromJust)

-- | Given a typing environment and an expression, compute the type of
-- the expression as quickly as possible, assuming that the expression
-- is well formed with correct type annotations.
fastTypeOf :: Map QName Schema -> Expr -> Type
fastTypeOf tyenv expr =
  case expr of
    -- Monomorphic fragment
    EList es t    -> tSeq (tNum (length es)) t
    ETuple es     -> tTuple (map (fastTypeOf tyenv) es)
    ERec fields   -> tRec [ (name, fastTypeOf tyenv e) | (name, e) <- fields ]
    ESel e sel    -> typeSelect (fastTypeOf tyenv e) sel
    EIf _ e _     -> fastTypeOf tyenv e
    EComp t _ _   -> t
    EAbs x t e    -> tFun t (fastTypeOf (Map.insert x (Forall [] [] t) tyenv) e)
    EApp e _      -> case tIsFun (fastTypeOf tyenv e) of
                        Just (_, t) -> t
                        Nothing     -> panic "Cryptol.TypeCheck.TypeOf.fastTypeOf"
                                         [ "EApp with non-function operator" ]
    ECast _ t     -> t
    -- Polymorphic fragment
    ECon      {}  -> polymorphic
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

fastSchemaOf :: Map QName Schema -> Expr -> Schema
fastSchemaOf tyenv expr =
  case expr of
    -- Polymorphic fragment
    ECon econ      -> typeOf econ
    EVar x         -> fromJust (Map.lookup x tyenv)
    ETAbs tparam e -> case fastSchemaOf tyenv e of
                        Forall tparams props ty -> Forall (tparam : tparams) props ty
    ETApp e t      -> case fastSchemaOf tyenv e of
                        Forall (tparam : tparams) props ty -> Forall tparams (apSubst s props) (apSubst s ty)
                                                                where s = singleSubst (tpVar tparam) t
                        _ -> panic "Cryptol.TypeCheck.TypeOf.fastSchemaOf"
                               [ "ETApp body with no type parameters" ]
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
    ESel   {}      -> monomorphic
    EIf    {}      -> monomorphic
    EComp  {}      -> monomorphic
    EApp   {}      -> monomorphic
    EAbs   {}      -> monomorphic
    ECast  {}      -> monomorphic
  where
    monomorphic = Forall [] [] (fastTypeOf tyenv expr)

-- | Yields the return type of the selector on the given argument type.
typeSelect :: Type -> Selector -> Type
typeSelect (TUser _ _ ty) sel = typeSelect ty sel
typeSelect (TCon _tctuple ts) (TupleSel i _) = ts !! i
typeSelect (TRec fields) (RecordSel n _) = fromJust (lookup n fields)
typeSelect (TCon _tcseq [_, a]) (ListSel _ _) = a
typeSelect ty _ = panic "Cryptol.TypeCheck.TypeOf.typeSelect"
                    [ "cannot apply selector to value of type", render (pp ty) ]

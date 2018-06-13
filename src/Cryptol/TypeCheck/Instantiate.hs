-- |
-- Module      :  Cryptol.TypeCheck.Instantiate
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.TypeCheck.Instantiate (instantiateWith) where

import Cryptol.ModuleSystem.Name (nameIdent)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Monad
import Cryptol.TypeCheck.Subst (listSubst,apSubst)
import Cryptol.TypeCheck.Error
import Cryptol.Parser.Position (Located(..))
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.PP

import Data.Function (on)
import Data.List(sortBy, groupBy, find)
import Data.Maybe(mapMaybe,isJust)
import Data.Either(partitionEithers)


instantiateWith :: Expr -> Schema -> [Located (Maybe Ident,Type)]
                -> InferM (Expr,Type)
instantiateWith e s ts
  | null named      = instantiateWithPos e s positional
  | null positional = instantiateWithNames e s named
  | otherwise       = do recordError CannotMixPositionalAndNamedTypeParams
                         instantiateWithNames e s named

  where
  (named,positional) = partitionEithers (map classify ts)
  classify t = case thing t of
                 (Just n,ty)  -> Left t { thing = (n,ty) }
                 (Nothing,ty) -> Right ty


instantiateWithPos :: Expr -> Schema -> [Type] -> InferM (Expr,Type)
instantiateWithPos e (Forall as ps t) ts =
  do su <- makeSu (1::Int) [] as ts
     doInst su e ps t
  where
  isNamed q = isJust (tpName q)

  makeSu n su (q : qs) (ty : tys)
    | not (isNamed q) = do r <- unnamed n q
                           makeSu (n+1) (r : su) qs (ty : tys)
    | k1 == k2        = makeSu (n+1) ((tpVar q, ty) : su) qs tys
    | otherwise       = do recordError $ KindMismatch k1 k2
                           r <- unnamed n q
                           makeSu (n+1) (r : su) qs tys
      where k1 = kindOf q
            k2 = kindOf ty

  makeSu _ su [] []       = return (reverse su)
  makeSu n su (q : qs) [] = do r <- unnamed n q
                               makeSu (n+1) (r : su) qs []
  makeSu _ su [] _        = do recordError TooManyPositionalTypeParams
                               return (reverse su)

  unnamed n q = do let src = ordinal n <+> text "type parameter"
                           $$ text "of" <+> ppUse e
                   ty <- newType src (kindOf q)
                   return (tpVar q, ty)




{- | Instantiate an expression of the given polymorphic type.
The arguments that are provided will be instantiated as requested,
the rest will be instantiated with fresh type variables.

EProofApp (ETApp e t)

  where
  - There will be one `ETApp t` for each insantiated type parameter;
  - there will be one `EProofApp` for each constraint on the schema;
-}
instantiateWithNames :: Expr -> Schema -> [Located (Ident,Type)]
                     -> InferM (Expr,Type)
instantiateWithNames e (Forall as ps t) xs =
  do sequence_ repeatedParams
     mapM_ (recordError . UndefinedTypeParameter . fmap fst) undefParams
     su' <- mapM paramInst as
     doInst su' e ps t
  where
  -- Choose the type for type parameter `x`
  paramInst x     =
    do let v = tpVar x
           k = kindOf v

           -- We just use nameIdent for comparison here, as all parameter names
           -- should have a NameInfo of Parameter.
           lkp name = find (\th -> fst (thing th) == nameIdent name) xs
           src = text "type parameter" <+> (case tpName x of
                                              Just n -> quotes (pp n)
                                              Nothing -> empty)
                                        $$ text "of" <+> ppUse e
       ty <- case lkp =<< tpName x of
               Just lty
                 | k1 == k   -> return ty
                 | otherwise -> inRange (srcRange lty) $
                                  do recordError (KindMismatch k k1)
                                     newType src k
                  where ty = snd (thing lty)
                        k1 = kindOf ty
               Nothing -> newType src k
       return (v,ty)

  -- Errors from multiple values for the same parameter.
  repeatedParams  = mapMaybe isRepeated
                  $ groupBy ((==) `on` pName)
                  $ sortBy (compare `on` pName) xs

  isRepeated ys@(a : _ : _)  =
    Just $ recordError (RepeatedTypeParameter (fst (thing a)) (map srcRange ys))
  isRepeated _ = Nothing


  paramIdents = [ nameIdent n | Just n <- map tpName as ]

  -- Errors from parameters that are defined, but do not exist in the schema.
  undefParams     = [ x | x <- xs, pName x `notElem` paramIdents ]

  pName = fst . thing





doInst :: [(TVar, Type)] -> Expr -> [Prop] -> Type -> InferM (Expr,Type)
doInst su' e ps t =
  do let su = listSubst su'
     newGoals (CtInst e) (map (apSubst su) ps)
     let t1 = apSubst su t
     return ( addProofParams
            $ addTyParams (map snd su') e
            , t1)
  where
  -- Add type parameters
  addTyParams ts e1 = foldl ETApp e1 ts

  -- Add proof parameters (the proofs are ommited but we mark where they'd go)
  addProofParams e1 = foldl (\e2 _ -> EProofApp e2) e1 ps





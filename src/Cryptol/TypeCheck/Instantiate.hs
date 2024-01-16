-- |
-- Module      :  Cryptol.TypeCheck.Instantiate
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# Language OverloadedStrings #-}
module Cryptol.TypeCheck.Instantiate
  ( instantiateWith
  , TypeArg(..)
  , uncheckedTypeArg
  , MaybeCheckedType(..)
  , instantiatePCon
  ) where

import Cryptol.ModuleSystem.Name (nameIdent)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Monad
import Cryptol.TypeCheck.Subst (listParamSubst, apSubst)
import Cryptol.TypeCheck.Kind(checkType)
import Cryptol.TypeCheck.Error
import Cryptol.Parser.Position (Located(..))
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Panic(panic)
import qualified Cryptol.Parser.AST as P

import Control.Monad(zipWithM)
import Data.Function (on)
import Data.List(sortBy, groupBy, find)
import Data.Maybe(mapMaybe,isJust)
import Data.Either(partitionEithers)
import qualified Data.Set as Set


data TypeArg = TypeArg
  { tyArgName :: Maybe (Located Ident)
  , tyArgType :: MaybeCheckedType
  }

uncheckedTypeArg :: P.TypeInst Name -> TypeArg
uncheckedTypeArg a =
  case a of
    P.NamedInst x ->
      TypeArg { tyArgName = Just (P.name x), tyArgType = Unchecked (P.value x) }
    P.PosInst t ->
      TypeArg { tyArgName = Nothing, tyArgType = Unchecked t }


data MaybeCheckedType = Checked Type | Unchecked (P.Type Name)



checkTyParam :: TypeSource -> Kind -> MaybeCheckedType -> InferM Type
checkTyParam src k mb =
  case mb of
    Checked t
      | k == k'   -> pure t
      | otherwise -> do recordError (KindMismatch (Just src) k k')
                        newType src k
        where k' = kindOf t
    Unchecked t -> checkType t (Just k)

-- | Instantiate a pattern constructor.  Returns (A,B,C,D) where:
-- A) are the instantiations of the type parameters of the constructor
-- B) is how many proofs we would have if we had dictionaries
-- C) are the types of the fields of the constructor
-- C) is the type of the result of the constructor (i.e., what we are mathcing)
instantiatePCon :: Name -> InferM ([Type],Int,[Type],Type)
instantiatePCon nm =
  do vart <- lookupVar nm
     case vart of
       CurSCC {} -> panic "instantiatePCon" [ "CurSCC"]
       ExtVar s ->
         do (e,t) <- instantiateWith nm (EVar nm) s []
            let (_, tApps, proofApps) = splitExprInst e
                (fs,res) = splitFun t
            pure (tApps, proofApps,fs,res)
  where
  splitFun ty =
    case tIsFun ty of
      Nothing -> ([], ty)
      Just (a,b) -> (a:as,c)
        where (as,c) = splitFun b

instantiateWith :: Name -> Expr -> Schema -> [TypeArg] -> InferM (Expr,Type)
instantiateWith nm e s ts
  | null named      = instantiateWithPos nm e s positional
  | null positional = instantiateWithNames nm e s named
  | otherwise       = do recordError CannotMixPositionalAndNamedTypeParams
                         instantiateWithNames nm e s named

  where
  (named,positional) = partitionEithers (map classify ts)
  classify t = case tyArgName t of
                 Just n  -> Left n { thing = (thing n, tyArgType t) }
                 Nothing -> Right (tyArgType t)



instantiateWithPos ::
  Name -> Expr -> Schema -> [MaybeCheckedType] -> InferM (Expr,Type)
instantiateWithPos nm e (Forall as ps t) ts =
  do su <- makeSu (1::Int) [] as ts
     doInst su e ps t
  where
  isNamed q = isJust (tpName q)

  makeSu n su (q : qs) (mbty : tys)
    | not (isNamed q) = do r <- unnamed n q
                           makeSu (n+1) (r : su) qs (mbty : tys)
    | otherwise = do ty <- checkTyParam (TypeParamInstPos nm n) (kindOf q) mbty
                     makeSu (n+1) ((q,ty) : su) qs tys

  makeSu _ su [] []       = return (reverse su)
  makeSu n su (q : qs) [] = do r <- unnamed n q
                               makeSu (n+1) (r : su) qs []
  makeSu _ su [] _        = do recordError TooManyPositionalTypeParams
                               return (reverse su)

  unnamed n q = do ty <- newType src (kindOf q)
                   return (q, ty)
    where
    src = case drop (n-1) {- count from 1 -} as of
            p:_ ->
              case tpName p of
                Just a -> TypeParamInstNamed nm (nameIdent a)
                _      -> TypeParamInstPos nm n
            _ -> panic "instantiateWithPos"
                    [ "Invalid parameter index", show n, show as ]





{- | Instantiate an expression of the given polymorphic type.
The arguments that are provided will be instantiated as requested,
the rest will be instantiated with fresh type variables.

EProofApp (ETApp e t)

  where
  - There will be one `ETApp t` for each insantiated type parameter;
  - there will be one `EProofApp` for each constraint on the schema;
-}
instantiateWithNames ::
  Name -> Expr -> Schema -> [Located (Ident,MaybeCheckedType)]
                     -> InferM (Expr,Type)
instantiateWithNames nm e (Forall as ps t) xs =
  do sequence_ repeatedParams
     mapM_ (recordError . UndefinedTypeParameter . fmap fst) undefParams
     su' <- zipWithM paramInst [ 1.. ] as
     doInst su' e ps t
  where
  -- Choose the type for type parameter `x`
  paramInst n x =
    do let k = tpKind x

           -- We just use nameIdent for comparison here, as all parameter names
           -- should have a NameInfo of Parameter.
           lkp name = find (\th -> fst (thing th) == nameIdent name) xs
           src = case tpName x of
                   Just na -> TypeParamInstNamed nm (nameIdent na)
                   Nothing -> TypeParamInstPos nm n
       ty <- case lkp =<< tpName x of
               Just lty -> checkTyParam src k (snd (thing lty))
               Nothing -> newType src k
       return (x, ty)

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



-- If the instantiation contains an assignment (v := t), and the type
-- contains a free unification variable ?x that could possibly depend
-- on v, then we must require that t = v (i.e. su must be an identity
-- substitution). Otherwise, this causes a problem: If ?x is
-- eventually instantiated to a type containing v, then the type
-- substitution will have computed the wrong result.

doInst :: [(TParam, Type)] -> Expr -> [Prop] -> Type -> InferM (Expr,Type)
doInst su' e ps t =
  do let su = listParamSubst su'
     newGoals (CtInst e) (map (apSubst su) ps)
     let t1 = apSubst su t

     -- Possibly more goals due to unification
     ps' <- concat <$> mapM checkInst su'
     newGoals (CtInst e) ps'

     return ( addProofParams (addTyParams (map snd su') e), t1 )
  where
  -- Add type parameters
  addTyParams ts e1 = foldl ETApp e1 ts

  -- Add proof parameters (the proofs are omitted but we mark where they'd go)
  addProofParams e1 = foldl (\e2 _ -> EProofApp e2) e1 ps

  -- free unification variables used in the schema
  frees = Set.unions (map fvs (t : ps))

  -- the bound variables from the scopes of any unification variables in the schema
  bounds = Set.unions (map scope (Set.toList frees))
    where
      scope (TVFree _ _ vs _) = vs
      scope (TVBound _) = Set.empty

  -- if the tvar is in 'bounds', then make sure it is an identity substitution
  checkInst :: (TParam, Type) -> InferM [Prop]
  checkInst (tp, ty)
    | Set.notMember tp bounds = return []
    | otherwise = let a   = tpVar tp
                      src = tvarDesc (tvInfo a)
                      rng = Just (tvarSource (tvInfo a))
                  in unify (WithSource (TVar a) src rng) ty


-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE PatternGuards, Safe #-}
module Cryptol.TypeCheck.Solver.Selector (tryHasGoal) where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Monad( InferM, unify, newGoals, lookupNewtype
                              , newType, applySubst, solveHasGoal
                              , newParamName
                              )
import Cryptol.TypeCheck.Subst(listSubst,apSubst)
import Cryptol.Utils.Ident (Ident, packIdent)
import Cryptol.Utils.PP(text,pp,ordinal,(<+>))
import Cryptol.Utils.Panic(panic)

import Control.Monad(forM,guard)


recordType :: [Ident] -> InferM Type
recordType labels =
  do fields <- forM labels $ \l ->
        do t <- newType (text "record field" <+> pp l) KType
           return (l,t)
     return (TRec fields)

tupleType :: Int -> InferM Type
tupleType n =
  do fields <- mapM (\x -> newType (ordinal x <+> text "tuple field") KType)
                    [ 0 .. (n-1) ]
     return (tTuple fields)

listType :: Int -> InferM Type
listType n =
  do elems <- newType (text "sequence element type") KType
     return (tSeq (tNum n) elems)


improveSelector :: Selector -> Type -> InferM Bool
improveSelector sel outerT =
  case sel of
    RecordSel _ mb -> cvt recordType mb
    TupleSel  _ mb -> cvt tupleType  mb
    ListSel   _ mb -> cvt listType   mb
  where
  cvt _ Nothing   = return False
  cvt f (Just a)  = do ty <- f a
                       newGoals CtExactType =<< unify ty outerT
                       newT <- applySubst outerT
                       return (newT /= outerT)


{- | Compute the type of a field based on the selector.
The given type should be "zonked" (i.e., substitution was applied to it),
and (outermost) type synonyms have been expanded.
-}
solveSelector :: Selector -> Type -> InferM (Maybe Type)
solveSelector sel outerT =
  case (sel, outerT) of

    (RecordSel l _, ty) ->
      case ty of
        TRec fs  -> return (lookup l fs)
        TCon (TC TCSeq) [len,el] -> liftSeq len el
        TCon (TC TCFun) [t1,t2]  -> liftFun t1 t2
        TCon (TC (TCNewtype (UserTC x _))) ts ->
          do mb <- lookupNewtype x
             case mb of
               Nothing -> return Nothing
               Just nt ->
                 case lookup l (ntFields nt) of
                   Nothing -> return Nothing
                   Just t  ->
                     do let su = listSubst (zip (map tpVar (ntParams nt)) ts)
                        newGoals (CtPartialTypeFun $ UserTyFun x)
                          $ apSubst su $ ntConstraints nt
                        return $ Just $ apSubst su t
        _ -> return Nothing

    (TupleSel n _, ty) ->
      case ty of

        TCon (TC (TCTuple m)) ts ->
          return $ do guard (0 <= n && n < m)
                      return $ ts !! n

        TCon (TC TCSeq) [len,el] -> liftSeq len el
        TCon (TC TCFun) [t1,t2]  -> liftFun t1 t2

        _ -> return Nothing


    (ListSel n _, TCon (TC TCSeq) [l,t])
      | n < 2 -> return (Just t)
      | otherwise ->
       do newGoals CtSelector [ l >== tNum (n - 1) ]
          return (Just t)

    _ -> return Nothing

  where
  liftSeq len el =
    do mb <- solveSelector sel (tNoUser el)
       return $ do el' <- mb
                   return (TCon (TC TCSeq) [len,el'])

  liftFun t1 t2 =
    do mb <- solveSelector sel (tNoUser t2)
       return $ do t2' <- mb
                   return (TCon (TC TCFun) [t1,t2'])


-- | Solve has-constraints.
tryHasGoal :: HasGoal -> InferM (Bool, Bool) -- ^ changes, solved
tryHasGoal has
  | TCon (PC (PHas sel)) [ th, ft ] <- goal (hasGoal has) =
    do imped     <- improveSelector sel th
       outerT    <- tNoUser `fmap` applySubst th
       mbInnerT  <- solveSelector sel outerT
       case mbInnerT of
         Nothing -> return (imped, False)
         Just innerT ->
           do newGoals CtExactType =<< unify innerT ft
              oT <- applySubst outerT
              iT <- applySubst innerT
              selFrom <- mkSel sel oT iT
              solveHasGoal (hasName has) selFrom
              return (True, True)

  | otherwise = panic "hasGoalSolved"
                  [ "Unexpected selector proposition:"
                  , show (hasGoal has)
                  ]

{- | Generator an appropriate selector, once the "Has" constraint
has been discharged.  The resulting selectors should always work
on their corresponding types (i.e., tuple selectros only select from tuples).
This function generates the code for lifting tuple/record selectors to sequences
and functions.

Assumes types are zonked. -}
mkSel :: Selector -> Type -> Type -> InferM (Expr -> Expr)
mkSel s outerT innerT =
  case tNoUser outerT of
    TCon (TC TCSeq) [len,el]
      | TupleSel {} <- s  -> liftSeq len el
      | RecordSel {} <- s -> liftSeq len el

    TCon (TC TCFun) [t1,t2]
      | TupleSel {} <- s -> liftFun t1 t2
      | RecordSel {} <- s -> liftFun t1 t2

    _ -> return (\e -> ESel e s)

  where
  liftSeq len el =
    do x <- newParamName (packIdent "x")
       case tNoUser innerT of
         TCon _ [_,eli] ->
           do selFrom <- mkSel s el eli
              return $ \e -> EComp len eli (selFrom (EVar x))
                                                        [[ From x len el e ]]
         _ -> panic "mkSel" [ "Unexpected inner seq type.", show innerT ]

  liftFun t1 t2 =
    do x <- newParamName (packIdent "x")
       case tNoUser innerT of
         TCon _ [_,inT] ->
           do selFrom <- mkSel s t2 inT
              return $ \e -> EAbs x t1 (selFrom (EApp e (EVar x)))
         _ -> panic "mkSel" [ "Unexpected inner fun type", show innerT ]





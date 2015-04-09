-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE PatternGuards, Safe #-}
module Cryptol.TypeCheck.Solver.Selector (tryHasGoal) where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Monad( InferM, unify, newGoals, lookupNewtype
                              , newType, applySubst, addHasGoal, solveHasGoal
                              )
import Cryptol.TypeCheck.Subst(listSubst,apSubst)
import Cryptol.Utils.PP(text,pp,ordinal,(<+>))
import Cryptol.Utils.Panic(panic)

import Control.Monad(forM,guard)


recordType :: [Name] -> InferM Type
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


improveSelector :: Selector -> Type -> InferM (Expr -> Expr)
improveSelector sel outerT =
  case sel of
    RecordSel _ mb -> cvt recordType mb
    TupleSel  _ mb -> cvt tupleType  mb
    ListSel   _ mb -> cvt listType   mb
  where
  cvt _ Nothing   = return id
  cvt f (Just a)  = do ty <- f a
                       cs <- unify ty outerT
                       case cs of
                         [] -> return id
                         _  -> do newGoals CtExactType cs
                                  return (`ECast` ty)


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





    (ListSel n _, TCon (TC TCSeq) [l,t])  ->
       do newGoals CtSelector [ (l .+. tNum (1::Int)) >== tNum n ]
          return (Just t)

    _ -> return Nothing

  where
  liftSeq len el =
    do mb <- solveSelector sel el
       return $ do el' <- mb
                   return (TCon (TC TCSeq) [len,el'])

  liftFun t1 t2 =
    do mb <- solveSelector sel t2
       return $ do t2' <- mb
                   return (TCon (TC TCFun) [t1,t2'])


-- | Solve has-constraints.
tryHasGoal :: HasGoal -> InferM ()
tryHasGoal has
  | TCon (PC (PHas sel)) [ th, ft ] <- goal (hasGoal has) =
    do outerCast <- improveSelector sel th
       outerT    <- tNoUser `fmap` applySubst th
       mbInnerT  <- solveSelector sel outerT
       case mbInnerT of
         Nothing -> addHasGoal has
         Just innerT ->
           do cs <- unify innerT ft
              innerCast <- case cs of
                             [] -> return id
                             _  -> do newGoals CtExactType cs
                                      return (`ECast` ft)
              solveHasGoal (hasName has) (innerCast . (`ESel` sel) . outerCast)

  | otherwise = panic "hasGoalSolved"
                  [ "Unexpected selector proposition:"
                  , show (hasGoal has)
                  ]




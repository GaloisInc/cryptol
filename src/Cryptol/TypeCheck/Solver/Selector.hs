-- |
-- Module      :  Cryptol.TypeCheck.Solver.Selector
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE PatternGuards, Safe #-}
module Cryptol.TypeCheck.Solver.Selector (tryHasGoal) where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Monad( InferM, unify, newGoals
                              , newType, applySubst, solveHasGoal
                              , newParamName
                              )
import Cryptol.TypeCheck.Subst (listParamSubst, apSubst)
import Cryptol.Utils.Ident (Ident, packIdent,Namespace(..))
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.RecordMap

import Control.Monad(forM,guard)


recordType :: [Ident] -> InferM Type
recordType labels =
  do fields <- forM labels $ \l ->
        do t <- newType (TypeOfRecordField l) KType
           return (l,t)
     return (TRec (recordFromFields fields))

tupleType :: Int -> InferM Type
tupleType n =
  do fields <- mapM (\x -> newType (TypeOfTupleField x) KType)
                    [ 0 .. (n-1) ]
     return (tTuple fields)

listType :: Int -> InferM Type
listType n =
  do elems <- newType TypeOfSeqElement KType
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
                       ps <- unify (WithSource outerT (selSrc sel)) ty
                       newGoals CtExactType ps
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
        TRec fs -> return (lookupField l fs)
        TNewtype nt ts ->
          case lookupField l (ntFields nt) of
            Nothing -> return Nothing
            Just t ->
              do let su = listParamSubst (zip (ntParams nt) ts)
                 newGoals (CtPartialTypeFun (ntName nt))
                   $ apSubst su $ ntConstraints nt
                 return $ Just $ apSubst su t

        TCon (TC TCSeq) [len,el] -> liftSeq len el
        TCon (TC TCFun) [t1,t2]  -> liftFun t1 t2
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
           do newGoals CtExactType =<< unify (WithSource innerT (selSrc sel)) ft
              oT <- applySubst outerT
              iT <- applySubst innerT
              sln <- mkSelSln sel oT iT
              solveHasGoal (hasName has) sln
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
mkSelSln :: Selector -> Type -> Type -> InferM HasGoalSln
mkSelSln s outerT innerT =
  case tNoUser outerT of
    TCon (TC TCSeq) [len,el]
      | TupleSel {} <- s  -> liftSeq len el
      | RecordSel {} <- s -> liftSeq len el

    TCon (TC TCFun) [t1,t2]
      | TupleSel {} <- s -> liftFun t1 t2
      | RecordSel {} <- s -> liftFun t1 t2

    _ -> return HasGoalSln { hasDoSelect = \e -> ESel e s
                           , hasDoSet    = \e v -> ESet outerT e s v }

  where
  -- Has s a t => Has s ([n]a) ([n]t)
  -- xs.s             ~~> [ x.s           | x <- xs ]
  -- { xs | s = ys }  ~~> [ { x | s = y } | x <- xs | y <- ys ]
  liftSeq len el =
    do x1 <- newParamName NSValue (packIdent "x")
       x2 <- newParamName NSValue (packIdent "x")
       y2 <- newParamName NSValue (packIdent "y")
       case tNoUser innerT of
         TCon _ [_,eli] ->
           do d <- mkSelSln s el eli
              pure HasGoalSln
                { hasDoSelect = \e ->
                    EComp len eli (hasDoSelect d (EVar x1))
                                  [[ From x1 len el e ]]
                , hasDoSet = \e v ->
                    EComp len el  (hasDoSet d (EVar x2) (EVar y2))
                                  [ [ From x2 len el  e ]
                                  , [ From y2 len eli v ]
                                  ]
                }


         _ -> panic "mkSelSln" [ "Unexpected inner seq type.", show innerT ]

  -- Has s b t => Has s (a -> b) (a -> t)
  -- f.s            ~~> \x -> (f x).s
  -- { f | s = g }  ~~> \x -> { f x | s = g x }
  liftFun t1 t2 =
    do x1 <- newParamName NSValue (packIdent "x")
       x2 <- newParamName NSValue (packIdent "x")
       case tNoUser innerT of
         TCon _ [_,inT] ->
           do d <- mkSelSln s t2 inT
              pure HasGoalSln
                { hasDoSelect = \e ->
                    EAbs x1 t1 (hasDoSelect d (EApp e (EVar x1)))
                , hasDoSet = \e v ->
                    EAbs x2 t1 (hasDoSet d (EApp e (EVar x2))
                                           (EApp v (EVar x2))) }
         _ -> panic "mkSelSln" [ "Unexpected inner fun type", show innerT ]





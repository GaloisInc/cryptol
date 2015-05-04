-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module implements a transformation, which tries to avoid exponential
-- slow down in some cases.  What's the problem?  Consider the following (common)
-- patterns:
--
--     fibs = [0,1] # [ x + y | x <- fibs, y <- drop`{1} fibs ]
--
-- The type of `fibs` is:
--
--     {a} (a >= 1, fin a) => [inf][a]
--
-- Here `a` is the number of bits to be used in the values computed by `fibs`.
-- When we evaluate `fibs`, `a` becomes a parameter to `fibs`, which works
-- except that now `fibs` is a function, and we don't get any of the memoization
-- we might expect!  What looked like an efficient implementation has all
-- of a sudden become exponential!
--
-- Note that this is only a problem for polymorphic values: if `fibs` was
-- already a function, it would not be that surprising that it does not
-- get cached.
--
-- So, to avoid this, we try to spot recursive polymorphic values,
-- where the recursive occurrences have the exact same type parameters
-- as the definition.  For example, this is the case in `fibs`: each
-- recursive call to `fibs` is instantiated with exactly the same
-- type parameter (i.e., `a`).  The rewrite we do is as follows:
--
--     fibs : {a} (a >= 1, fin a) => [inf][a]
--     fibs = \{a} (a >= 1, fin a) -> fibs'
--       where fibs' : [inf][a]
--             fibs' = [0,1] # [ x + y | x <- fibs', y <- drop`{1} fibs' ]
--
-- After the rewrite, the recursion is monomorphic (i.e., we are always using
-- the same type).  As a result, `fibs'` is an ordinary recursive value,
-- where we get the benefit of caching.
--
-- The rewrite is a bit more complex, when there are multiple mutually
-- recursive functions.  Here is an example:
--
--     zig : {a} (a >= 2, fin a) => [inf][a]
--     zig = [1] # zag
--
--     zag : {a} (a >= 2, fin a) => [inf][a]
--     zag = [2] # zig
--
-- This gets rewritten to:
--
--     newName : {a} (a >= 2, fin a) => ([inf][a], [inf][a])
--     newName = \{a} (a >= 2, fin a) -> (zig', zag')
--       where
--       zig' : [inf][a]
--       zig' = [1] # zag'
--
--       zag' : [inf][a]
--       zag' = [2] # zig'
--
--     zig : {a} (a >= 2, fin a) => [inf][a]
--     zig = \{a} (a >= 2, fin a) -> (newName a <> <> ).1
--
--     zag : {a} (a >= 2, fin a) => [inf][a]
--     zag = \{a} (a >= 2, fin a) -> (newName a <> <> ).2
--
-- NOTE:  We are assuming that no capture would occur with binders.
-- For values, this is because we replaces things with freshly chosen variables.
-- For types, this should be because there should be no shadowing in the types.
-- XXX: Make sure that this really is the case for types!!

{-# LANGUAGE PatternGuards, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
module Cryptol.Transform.MonoValues (rewModule) where

import Cryptol.Parser.AST (Pass(MonoValues))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.TypeMap
import Data.List(sortBy,groupBy)
import Data.Either(partitionEithers)
import Data.Map (Map)
import MonadLib

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

{- (f,t,n) |--> x  means that when we spot instantiations of `f` with `ts` and
`n` proof argument, we should replace them with `Var x` -}
newtype RewMap' a = RM (Map QName (TypesMap (Map Int a)))
type RewMap = RewMap' QName

instance TrieMap RewMap' (QName,[Type],Int) where
  emptyTM  = RM emptyTM

  nullTM (RM m) = nullTM m

  lookupTM (x,ts,n) (RM m) = do tM <- lookupTM x m
                                tP <- lookupTM ts tM
                                lookupTM n tP

  alterTM (x,ts,n) f (RM m) = RM (alterTM x f1 m)
    where
    f1 Nothing   = do a <- f Nothing
                      return (insertTM ts (insertTM n a emptyTM) emptyTM)

    f1 (Just tM) = Just (alterTM ts f2 tM)

    f2 Nothing   = do a <- f Nothing
                      return (insertTM n a emptyTM)

    f2 (Just pM) = Just (alterTM n f pM)

  unionTM f (RM a) (RM b) = RM (unionTM (unionTM (unionTM f)) a b)

  toListTM (RM m) = [ ((x,ts,n),y) | (x,tM)  <- toListTM m
                                   , (ts,pM) <- toListTM tM
                                   , (n,y)   <- toListTM pM ]

  mapMaybeWithKeyTM f (RM m) =
    RM (mapWithKeyTM      (\qn  tm ->
        mapWithKeyTM      (\tys is ->
        mapMaybeWithKeyTM (\i   a  -> f (qn,tys,i) a) is) tm) m)

-- | Note that this assumes that this pass will be run only once for each
-- module, otherwise we will get name collisions.
rewModule :: Module -> Module
rewModule m = fst
            $ runId
            $ runStateT 0
            $ runReaderT (Just (mName m))
            $ do ds <- mapM (rewDeclGroup emptyTM) (mDecls m)
                 return m { mDecls = ds }

--------------------------------------------------------------------------------

type M      = ReaderT RO (StateT RW Id)

type RO = Maybe ModName   -- are we at the top level?
type RW = Int             -- to generate names

newName :: M QName
newName =
  do n  <- sets $ \s -> (s, s + 1)
     seq n $ return (QName Nothing (NewName MonoValues n))

newTopOrLocalName :: M QName
newTopOrLocalName =
  do mb <- ask
     n  <- sets $ \s -> (s, s + 1)
     seq n $ return (QName mb (NewName MonoValues n))

inLocal :: M a -> M a
inLocal = local Nothing



--------------------------------------------------------------------------------
rewE :: RewMap -> Expr -> M Expr   -- XXX: not IO
rewE rews = go

  where
  tryRewrite (EVar x,tps,n) =
     do y <- lookupTM (x,tps,n) rews
        return (EVar y)
  tryRewrite _ = Nothing

  go expr =
    case expr of

      -- Interesting cases
      ETApp e t      -> case tryRewrite (splitTApp expr 0) of
                          Nothing  -> ETApp <$> go e <*> return t
                          Just yes -> return yes
      EProofApp e    -> case tryRewrite (splitTApp e 1) of
                          Nothing  -> EProofApp <$> go e
                          Just yes -> return yes

      ECon {}         -> return expr
      EList es t      -> EList   <$> mapM go es <*> return t
      ETuple es       -> ETuple  <$> mapM go es
      ERec fs         -> ERec    <$> (forM fs $ \(f,e) -> do e1 <- go e
                                                             return (f,e1))
      ESel e s        -> ESel    <$> go e  <*> return s
      EIf e1 e2 e3    -> EIf     <$> go e1 <*> go e2 <*> go e3

      EComp t e mss   -> EComp t <$> go e  <*> mapM (mapM (rewM rews)) mss
      EVar _          -> return expr

      ETAbs x e       -> ETAbs x  <$> go e

      EApp e1 e2      -> EApp     <$> go e1 <*> go e2
      EAbs x t e      -> EAbs x t <$> go e

      EProofAbs x e   -> EProofAbs x <$> go e

      ECast e t       -> ECast       <$> go e <*> return t
      EWhere e dgs    -> EWhere      <$> go e <*> inLocal
                                                  (mapM (rewDeclGroup rews) dgs)


rewM :: RewMap -> Match -> M Match
rewM rews ma =
  case ma of
    From x t e -> From x t <$> rewE rews e

    -- These are not recursive.
    Let d      -> Let <$> rewD rews d


rewD :: RewMap -> Decl -> M Decl
rewD rews d = do e <- rewE rews (dDefinition d)
                 return d { dDefinition = e }

rewDeclGroup :: RewMap -> DeclGroup -> M DeclGroup
rewDeclGroup rews dg =
  case dg of
    NonRecursive d -> NonRecursive <$> rewD rews d
    Recursive ds ->
      do let (leave,rew) = partitionEithers (map consider ds)
             rewGroups   = groupBy sameTParams
                         $ sortBy compareTParams rew
         ds1 <- mapM (rewD rews) leave
         ds2 <- mapM rewSame rewGroups
         return $ Recursive (ds1 ++ concat ds2)

  where
  sameTParams    (_,tps1,x,_) (_,tps2,y,_) = tps1 == tps2 && x == y
  compareTParams (_,tps1,x,_) (_,tps2,y,_) = compare (x,tps1) (y,tps2)

  consider d   = let (tps,props,e) = splitTParams (dDefinition d)
                 in if not (null tps) && notFun e
                     then Right (d, tps, props, e)
                     else Left d

  rewSame ds =
     do new <- forM ds $ \(d,_,_,e) ->
                 do x <- newName
                    return (d, x, e)
        let (_,tps,props,_) : _ = ds
            tys            = map (TVar . tpVar) tps
            proofNum       = length props
            addRew (d,x,_) = insertTM (dName d,tys,proofNum) x
            newRews        = foldr addRew rews new

        newDs <- forM new $ \(d,newN,e) ->
                   do e1 <- rewE newRews e
                      return ( d
                             , d { dName        = newN
                                 , dSignature   = (dSignature d)
                                         { sVars = [], sProps = [] }
                                 , dDefinition  = e1
                                 }
                             )

        case newDs of
          [(f,f')] ->
              return  [ f { dDefinition =
                                let newBody = EVar (dName f')
                                    newE = EWhere newBody
                                              [ Recursive [f'] ]
                                in foldr ETAbs
                                   (foldr EProofAbs newE props) tps
                            }
                      ]

          _ -> do tupName <- newTopOrLocalName
                  let (polyDs,monoDs) = unzip newDs

                      tupAr  = length monoDs
                      addTPs = flip (foldr ETAbs)     tps
                             . flip (foldr EProofAbs) props

                      -- tuple = \{a} p -> (f',g')
                      --                where f' = ...
                      --                      g' = ...
                      tupD = Decl
                        { dName       = tupName
                        , dSignature  =
                            Forall tps props $
                               TCon (TC (TCTuple tupAr))
                                    (map (sType . dSignature) monoDs)

                        , dDefinition =
                            addTPs $
                            EWhere (ETuple [ EVar (dName d) | d <- monoDs ])
                                   [ Recursive monoDs ]

                        , dPragmas    = [] -- ?
                        }

                      mkProof e _ = EProofApp e

                      -- f = \{a} (p) -> (tuple @a p). n

                      mkFunDef n f =
                        f { dDefinition =
                              addTPs $ ESel ( flip (foldl mkProof) props
                                            $ flip (foldl ETApp) tys
                                            $ EVar tupName
                                            ) (TupleSel n (Just tupAr))
                          }

                  return (tupD : zipWith mkFunDef [ 0 .. ] polyDs)


--------------------------------------------------------------------------------
splitTParams :: Expr -> ([TParam], [Prop], Expr)
splitTParams e = let (tps, e1)   = splitWhile splitTAbs e
                     (props, e2) = splitWhile splitProofAbs e1
                 in (tps,props,e2)

-- returns type instantitaion and how many "proofs" were there
splitTApp :: Expr -> Int -> (Expr, [Type], Int)
splitTApp (EProofApp e) n = splitTApp e $! (n + 1)
splitTApp e0 n            = let (e1,ts) = splitTy e0 []
                            in (e1, ts, n)
  where
  splitTy (ETApp e t) ts = splitTy e (t:ts)
  splitTy e ts           = (e,ts)

notFun :: Expr -> Bool
notFun (EAbs {})       = False
notFun (EProofAbs _ e) = notFun e
notFun _               = True


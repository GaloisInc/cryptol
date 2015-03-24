-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains machinery to reason about ordering of
-- variables, their finiteness, and their possible intervals.

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
module Cryptol.TypeCheck.Solver.FinOrd
  ( OrdFacts, AssertResult(..)
  , noFacts, addFact
  , isKnownLeq
  , knownInterval
  , ordFactsToGoals
  , ordFactsToProps
  , dumpDot
  , dumpDoc
  , IsFact(..)
  ) where

import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.TypeCheck.Solver.Interval
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.InferTypes
import           Cryptol.TypeCheck.TypeMap
import           Cryptol.Parser.Position
import qualified Cryptol.Utils.Panic as P
import           Cryptol.Utils.PP(Doc,pp,vcat,text,(<+>))

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Maybe(fromMaybe,maybeToList)
import           Control.Monad(guard)

-- Please change this, if renaming the module.
panic :: String -> [String] -> a
panic x y = P.panic ("Cryptol.TypeCheck.Solver.FinOrd." ++ x) y


-- | Add a `(>=)` or `fin` goal into the model.
-- Assumes that the types are normalized (i.e., no type functions).
class IsFact t where
  factProp       :: t -> Prop
  factChangeProp :: t -> Prop -> t
  factSource     :: t -> EdgeSrc

instance IsFact Goal where
  factProp           = goal
  factChangeProp g p = g { goal = p }
  factSource g       = FromGoal (goalSource g) (goalRange g)

instance IsFact Prop where
  factProp           = id
  factChangeProp _ x = x
  factSource _       = NoGoal

addFact :: IsFact t => t -> OrdFacts -> AssertResult
addFact g m =
  case tNoUser (factProp g) of
    TCon (PC PFin) [t] ->
      let (x,m1) = nameTerm m t
      in insertFin src x m1

    TCon (PC PGeq) [t1,t2] ->
      let (x,m1) = nameTerm m  t1
          (y,m2) = nameTerm m1 t2
      in insertLeq src y x m2

    _ -> OrdCannot
  where
  src = factSource g


-- | Possible outcomes, when asserting a fact.
data AssertResult
  = OrdAdded OrdFacts       -- ^ We added a new fact
  | OrdAlreadyKnown         -- ^ We already knew this
  | OrdImprove Type Type    -- ^ Only if the two types are equal
  | OrdImpossible           -- ^ The fact is known to be false
  | OrdCannot               -- ^ We could not perform opertaion.
    deriving Show



-- | Query if the one type is known to be smaller than, or equal to, the other.
-- Assumes that the type is simple (i.e., no type functions).
isKnownLeq :: OrdFacts -> Type -> Type -> Bool
isKnownLeq m t1 t2 =
  let (x,m1) = nameTerm m  t1
      (y,m2) = nameTerm m1 t2
  in isLeq m2 x y


-- | Compute an interval, that we know definately contains the given type.
-- Assumes that the type is normalized (i.e., no type functions).
knownInterval :: OrdFacts -> Type -> Interval
knownInterval m t =
    fromMaybe anything $
    do a <- numType t
       return $
         case (cvtLower (getLowerBound m a), cvtUpper (getUpperBound m a)) of
           (x,(y,z)) -> Interval { lowerBound = x
                                 , upperBound = y
                                 , isFinite   = z
                                 }
  where
  cvtLower (Nat'' x) = Nat x
  cvtLower FinNat''  = panic "knownInterval"
                             [ "`FinNat` used as a lower bound for:"
                             , show t
                             ]
  cvtLower Inf''     = Inf

  cvtUpper (Nat'' x) = (Nat x, True)
  cvtUpper FinNat''  = (Inf,   True)
  cvtUpper Inf''     = (Inf,   False)


ordFactsToGoals :: OrdFacts -> [Goal]
ordFactsToGoals = ordFactsToList onlyGoals
  where
  onlyGoals (FromGoal c r) = Just $ \p -> Goal { goalSource = c
                                               , goalRange = r
                                               , goal = p }
  onlyGoals NoGoal         = Nothing

ordFactsToProps :: OrdFacts -> [Prop]
ordFactsToProps = ordFactsToList (\_ -> Just id)



ordFactsToList :: (EdgeSrc -> Maybe (Prop -> a)) -> OrdFacts -> [a]
ordFactsToList consider (OrdFacts m ts) = concatMap getGoals (Map.toList m)
  where
  getGoals (ty, es) =
    do (lower,notNum) <-
          case ty of
            NTNat FinNat''     -> []
            NTNat Inf''        -> []
            NTNat (Nat'' n)    -> guard (n > 0) >> [ (tNum n, False) ]
            NTVar v            -> [ (TVar v,  True) ]
            NTNamed x          -> [ (getNamed x, True) ]

       Edge { target = t, eSource = src } <- Set.toList (above es)
       f <- maybeToList (consider src)

       g <- case t of
              NTNat FinNat''     -> guard notNum >> [ pFin lower ]
              NTNat Inf''        -> []
              NTNat (Nat'' n)    -> guard notNum >> [ tNum n >== lower ]
              NTVar x            -> [ TVar x >== lower ]
              NTNamed x          -> [ getNamed x >== lower ]

       return (f g)

  getNamed x = case IntMap.lookup x (nameToType ts) of
                 Just t  -> t
                 Nothing -> panic "ordFactsToList" [ "Missing name" ]






--------------------------------------------------------------------------------


data OrdFacts     = OrdFacts (Map NumType Edges) OrdTerms
                    deriving Show

-- | Names for non-primitive terms
data OrdTerms     = OrdTerms
                    { typeToName :: TypeMap Int
                      -- ^ Maps terms to their name

                    , nameToType  :: IntMap Type
                      -- ^ Maps names to terms

                    , nextId  :: Int -- ^ For naming new terms.
                    } deriving Show


data Edges        = Edges { above :: Set Edge, below :: Set Edge }
                    deriving Show

data Edge         = Edge { target :: NumType, eSource :: EdgeSrc }
                    deriving Show

-- | Where did this edge come from?
-- This is used so that we can turn edges back into goals.
data EdgeSrc      = FromGoal ConstraintSource Range
                  | NoGoal
                    deriving Show

instance Eq Edge where
  x == y = target x == target y

instance Ord Edge where
  compare x y = compare (target x) (target y)

{- | A varaation on `Nat'`, which allows us to support `fin` constraints:
we add an extra element `FinNat''`, which is larger than all natural numbers,
but smaller than infinity.  Then, we can express `fin t` as `t <= fin`.
This is only internal to the implementation and is not visible outside
this module. -}
data Nat''        = Nat'' Integer
                  | FinNat''        -- Upper bound for known finite
                  | Inf''
                    deriving (Eq,Ord,Show)

-- NOTE: It is important that constants come before variables in the
-- ordering (used in `insNode`)
data NumType      = NTNat Nat'' | NTVar TVar | NTNamed Int
                    deriving (Eq,Ord,Show)

nameTerm :: OrdFacts -> Type -> (NumType, OrdFacts)
nameTerm fs t | Just n <- numType t = (n, fs)
nameTerm fs@(OrdFacts xs ts) t =
  case lookupTM t (typeToName ts) of
    Just n -> (NTNamed n, fs)
    Nothing ->
      let name = nextId ts
          ts1  = OrdTerms { nameToType = IntMap.insert name t (nameToType ts)
                          , typeToName = insertTM t name (typeToName ts)
                          , nextId     = name + 1
                          }

      in (NTNamed name, OrdFacts xs ts1)

zero :: NumType
zero = NTNat (Nat'' 0)

-- | A finite number larger than all ordinary numbers.
-- Used to represent `fin` predicates.
fin :: NumType
fin = NTNat FinNat''

inf :: NumType
inf = NTNat Inf''

numType :: Type -> Maybe NumType
numType ty =
  case tNoUser ty of
    TCon (TC (TCNum n)) _        -> Just $ NTNat $ Nat'' n
    TCon (TC TCInf) _            -> Just $ NTNat $ Inf''
    TVar x | kindOf x == KNum    -> Just $ NTVar x
    _                            -> Nothing

fromNumType :: OrdTerms -> NumType -> Maybe Type
fromNumType _ (NTVar x)         = Just (TVar x)
fromNumType _ (NTNat Inf'')     = Just tInf
fromNumType _ (NTNat FinNat'')  = Nothing
fromNumType _ (NTNat (Nat'' x)) = Just (tNum x)
fromNumType ts (NTNamed x)      = IntMap.lookup x (nameToType ts)

isVar :: NumType -> Bool
isVar (NTVar _)   = True
isVar (NTNamed _) = True
isVar (NTNat _)   = False

noFacts :: OrdFacts
noFacts = snd $ insNode inf
        $ snd $ insNode fin
        $ snd $ insNode zero
        $ OrdFacts Map.empty OrdTerms { typeToName = emptyTM
                                      , nameToType = IntMap.empty
                                      , nextId     = 0
                                      }

noEdges :: Edges
noEdges = Edges { above = Set.empty, below = Set.empty }

-- | Get the edges immediately above or bellow a node.
imm :: (Edges -> Set Edge) -> OrdFacts -> NumType -> Set Edge
imm dir (OrdFacts m _) t = maybe Set.empty dir (Map.lookup t m)


-- Try to find a path from one node to another.
reachable :: OrdFacts -> NumType -> NumType -> Bool
reachable m smaller larger =
  search Set.empty (Set.singleton Edge { target = smaller, eSource = NoGoal })
  where
  search visited todo
    | Just (Edge { target = term }, rest) <- Set.minView todo =
       if term == larger
         then True
         else let new = imm above m term
                  vis = Set.insert term visited
                  notDone = Set.filter (not . (`Set.member` vis) . target)
              in search vis (notDone new `Set.union` notDone rest)

    | otherwise = False



{-
The linking function is a bit complex because we keep the ordering database
minimal.

This diagram illustrates what we do when we link two nodes (`link`).

We start with a situation like on the left, and we are adding an
edge from L to U.  The final result is illustrated on the right.

   Before    After

     a         a
    /|        /
   / |       /
  U  |      U\
  |  L        \L
  | /         /
  |/         /
  d         d

L: lower
U: upper
a: a member of "above uedges"  (uus)
d: a member of "below ledges"  (lls)
-}

{- XXX: It would be useful to return the edges that were removed because these
edges can be solved in term of the existing facts, so if some of them correspond
to wanted constrainst we can discharge them straight aways.   We still get
the same effect in `reExamineWanteds` but in a much less effecieant way. -}


link :: EdgeSrc -> (NumType,Edges) -> (NumType,Edges)
      -> OrdFacts -> (Edges,Edges,OrdFacts)

link src (lower, ledges) (upper, uedges) m0 =

  let uus         = Set.mapMonotonic target (above uedges)
      lls         = Set.mapMonotonic target (below ledges)

      rm x        = Set.filter (not . (`Set.member` x) . target)

      {- As soon as we insert someghing above a node, we remove any
      links to `Inf''` because, inductively, the thing above will
      already be connected -}
      newLedges   = ledges { above = Set.insert Edge { target = upper
                                                     , eSource = src }
                                   $ rm (Set.insert inf uus) -- see comment
                                   $ above ledges
                           }
      newUedges   = uedges { below = Set.insert Edge { target = lower
                                                     , eSource = src }
                                   $ rm lls
                                   $ below uedges
                           }

      del x       = Set.delete Edge { target = x, eSource = NoGoal }

      adjust f t (OrdFacts m xs) = OrdFacts (Map.adjust f t m) xs
      insert k x (OrdFacts m xs) = OrdFacts (Map.insert k x m) xs
      adjAbove    = adjust (\e -> e { above = del upper (above e) })
      adjBelow    = adjust (\e -> e { below = del lower (below e) })
      fold f xs x = Set.fold f x xs

  in ( newLedges
     , newUedges
     , insert lower newLedges
     $ insert upper newUedges
     $ fold adjAbove lls
     $ fold adjBelow uus
       m0
     )



-- | Insert a new node in a collection of facts.
-- Returns the edges surrounding the new node.
--  * Variable nodes are always linked to 0 and Inf'' (directly or indirectly).
--  * Constant nodes are always linked to neighbouring constant nodes.
insNode :: NumType -> OrdFacts -> (Edges, OrdFacts)
insNode t model@(OrdFacts m0 xs) =
  case Map.splitLookup t m0 of
    (_, Just r, _)  -> (r, model)
    (left, Nothing, right) ->
      let m1 = OrdFacts (Map.insert t noEdges m0) xs
      in if isVar t

         -- New variabeles are always linkes to 0 and inf.
         then

            case Map.lookup zero m0 of
              Just zes ->
                let (_,es1,m2@(OrdFacts m2M _)) = link NoGoal (zero,zes) (t,noEdges) m1
                in case Map.lookup inf m2M of
                     Just ies ->
                        let (es2,_,m3) = link NoGoal (t,es1) (inf,ies) m2
                        in (es2,m3)
                     Nothing -> panic "insNode"
                                  [ "infinity is missing from the model"
                                  , show m0
                                  ]
              Nothing -> panic "insNode"
                           [ "0 is missing from the model"
                           , show m0
                           ]

         -- Constants are linked to their neighbours.
         else

             -- link to a smaller constnat, if any
             let ans2@(es2, m2) =
                   case toNum Map.findMax left of
                     Nothing -> (noEdges,m1)
                     Just l  ->
                       let (_,x,y) = link NoGoal l (t,noEdges) m1
                       in (x,y)

             -- link to a larger constant, if any
             in case toNum Map.findMin right of
                  Nothing -> ans2
                  Just u  ->
                    let (x,_,y) = link NoGoal (t,es2) u m2
                    in (x,y)

  where
  toNum f x = do guard (not (Map.null x))
                 let it@(n,_) = f x
                 guard (not (isVar n))
                 return it


isLeq :: OrdFacts -> NumType -> NumType -> Bool
isLeq m t1 t2 = reachable m2 t1 t2
  where (_,m1) = insNode t1 m
        (_,m2) = insNode t2 m1


insertLeq :: EdgeSrc -> NumType -> NumType -> OrdFacts -> AssertResult
insertLeq _ (NTNat Inf'') (NTNat Inf'') _       = OrdAlreadyKnown
insertLeq _ (NTNat Inf'') (NTNat FinNat'')  _   = OrdImpossible
insertLeq _ (NTNat Inf'') (NTNat (Nat'' _)) _   = OrdImpossible

insertLeq _ (NTNat FinNat'') (NTNat Inf'') _    = OrdAlreadyKnown
insertLeq _ (NTNat FinNat'') (NTNat FinNat'') _ = OrdAlreadyKnown -- can't happen
insertLeq _ (NTNat FinNat'') (NTNat (Nat'' _)) _= OrdImpossible   -- ditto

insertLeq _ (NTNat (Nat'' _)) (NTNat Inf'') _     = OrdAlreadyKnown
insertLeq _ (NTNat (Nat'' _)) (NTNat FinNat'')  _ = OrdAlreadyKnown
insertLeq _ (NTNat (Nat'' x)) (NTNat (Nat'' y)) _
  | x <= y    = OrdAlreadyKnown
  | otherwise = OrdImpossible


insertLeq src t1 t2 m0
  | reachable m2 t2 t1 = case (fromNumType terms t1, fromNumType terms t2) of
                           (Just a, Just b) -> OrdImprove a b
                           _                -> OrdCannot  -- should not happen
  | otherwise =
     if reachable m2 t1 t2
       then OrdAlreadyKnown
       else let (_,_,m3) = link src (t1,n1) (t2,n2) m2
            in OrdAdded m3
  where (_,m1)   = insNode t1 m0
        (n2,m2@(OrdFacts m2M terms))  = insNode t2 m1
        Just n1 = Map.lookup t1 m2M

insertFin :: EdgeSrc -> NumType -> OrdFacts -> AssertResult
insertFin src t m = insertLeq src t (NTNat FinNat'') m


getLowerBound :: OrdFacts -> NumType -> Nat''
getLowerBound _ (NTNat n) = n
getLowerBound fs@(OrdFacts m _) t =
  case Map.lookup t m of
    Nothing -> Nat'' 0
    Just es -> case map (getLowerBound fs . target) $ Set.toList $ below es of
                 [] -> Nat'' 0
                 xs -> maximum xs

getUpperBound :: OrdFacts -> NumType -> Nat''
getUpperBound _ (NTNat n) = n
getUpperBound fs@(OrdFacts m _) t =
  case Map.lookup t m of
    Nothing -> Inf''
    Just es -> case map (getUpperBound fs . target) $ Set.toList $ above es of
                 [] -> Inf''
                 xs -> minimum xs




--------------------------------------------------------------------------------
-- Testing

-- | Render facts in `dot` notation. The boolean says if we want the arrows
-- to point up.
dumpDot :: Bool -> OrdFacts -> String
dumpDot isUp (OrdFacts m _) = "digraph {" ++ concatMap edges (Map.toList m) ++ "}"
  where
  edge x e = x ++ " -> " ++ node (target e) ++ "[color=\"blue\"];"
  dir = if isUp then above else below
  edges (x,es) = let n = node x
                 in n ++ ";" ++
                    concatMap (edge n) (Set.toList (dir es))

  node (NTNat (Nat'' x))            = show (show x)
  node (NTNat FinNat'')             = show "fin"
  node (NTNat Inf'')                = show "inf"
  node (NTVar (TVFree x _ _ _))     = show ("?v" ++ show x)
  node (NTVar (TVBound x _))        = show ("v" ++ show x)
  node (NTNamed x)                  = show ("<" ++ show x ++ ">")

dumpDoc :: OrdFacts -> Doc
dumpDoc = vcat . ordFactsToList mk
  where
  mk src = Just $ \x -> case src of
                          NoGoal      -> text "[G]" <+> pp x
                          FromGoal {} -> text "[W]" <+> pp x


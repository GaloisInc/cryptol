{-# LANGUAGE Safe, RecordWildCards #-}
{- | Separate Non-Linear Constraints
When we spot a non-linear expression, we name it and add it to a map.

If we see the same expression multiple times, then we give it the same name.

The body of the non-linear expression is not processed further,
so the resulting map should not contain any of the newly minted names.
-}

module Cryptol.TypeCheck.Solver.Numeric.NonLin
  ( nonLinProp
  , NonLinS, nonLinSubst
  , initialNonLinS
  , apSubstNL
  , lookupNL
  ) where

import Cryptol.TypeCheck.Solver.Numeric.AST
import Cryptol.TypeCheck.Solver.Numeric.Simplify
import Cryptol.TypeCheck.Solver.Numeric.SimplifyExpr
import Cryptol.Utils.Panic(panic)

-- import           Data.GenericTrie (Trie)
-- import qualified Data.GenericTrie as Trie
import           Data.Maybe ( fromMaybe )
import           MonadLib
import           Data.Map (Map)
import qualified Data.Map as Map

type Trie   = Map

trie_empty  = Map.empty
trie_insert = Map.insert
trie_delete = Map.delete
trie_lookup = Map.lookup


-- | Factor-out non-linear terms, by naming them.
nonLinProp :: NonLinS -> Prop -> ([Prop], NonLinS)
nonLinProp s0 prop = (p : ps, s)
  where ((p,ps),s) = runNL s0 (nonLinPropM prop)

{- | Apply a substituin to the non-linear expression database.
Returns `Nothing` if nothing was affected.
Otherwise returns `Just`, and a substitution for non-linear expressions
that became linear.

The definitions of NL terms do not contain other named NL terms,
so it does not matter if the substitution contains bindings like @_a = e@.

There should be no bindings that mention NL term names in the definitions
of the substition (i.e, things like @x = _a@ are NOT ok).
-}
apSubstNL :: Subst -> NonLinS -> Maybe (Subst, [Prop], NonLinS)
apSubstNL su s0 = case runNL s0 (mApSubstNL su) of
                    ((Nothing,_),_) -> Nothing
                    ((Just su1,ps),r) -> Just (su1,ps,r)

lookupNL :: Name -> NonLinS -> Maybe Expr
lookupNL x NonLinS { .. } = Map.lookup x nonLinExprs


runNL :: NonLinS -> NonLinM a -> ((a, [Prop]), NonLinS)
runNL s m = runId
          $ runStateT s 
          $ do a  <- m
               ps <- finishTodos
               return (a,ps)

-- | Get the known non-linear terms.
nonLinSubst :: NonLinS -> Subst
nonLinSubst = nonLinExprs

-- | The initial state for the linearization process.
initialNonLinS :: NonLinS
initialNonLinS = NonLinS
  { nextName = 0
  , nonLinExprs = Map.empty
  , nlKnown = trie_empty
  , nlTodo = []
  }


data SubstOneRes = NoChange
                   -- ^ Substitution does not affect the expression.

                 | Updated (Maybe (Name,Expr))
                   -- ^ The expression was updated and, maybe, it became linear.


{- | Apply the substituint to all non-linear bindings.
Returns `Nothing` if nothing was affected.
Otherwise returns `Just`, and a substituion mapping names that used
to be non-linear but became linear.

Note that we may return `Just empty`, indicating that some non-linear
expressions were updated, but they remained non-linear. -}
mApSubstNL :: Subst -> NonLinM (Maybe Subst)
mApSubstNL su =
  do s <- get
     answers <- mapM (mApSubstOneNL su) (Map.toList (nonLinExprs s))
     return (foldr upd Nothing answers)
  where
  upd NoChange ch     = ch
  upd (Updated mb) ch = let lsu = fromMaybe Map.empty ch
                        in Just (case mb of
                                   Nothing    -> lsu
                                   Just (x,e) -> Map.insert x e lsu)


mApSubstOneNL :: Subst -> (Name,Expr) -> NonLinM SubstOneRes
mApSubstOneNL su (x,e) =
  case apSubst su e of
    Nothing -> return NoChange
    Just e1 ->
      case crySimpExprMaybe e1 of

        Nothing ->
          sets $ \NonLinS { .. } ->
            ( Updated Nothing
            , NonLinS { nonLinExprs = Map.insert x e1 nonLinExprs
                      , nlKnown = trie_insert e1 x (trie_delete e nlKnown)
                      , .. }
            )

        Just e2
          | isNonLinOp e2 ->
          sets $ \NonLinS { .. } ->
            (Updated Nothing
            , NonLinS { nonLinExprs = Map.insert x e2 nonLinExprs
                      , nlKnown = trie_insert e2 x (trie_delete e nlKnown)
                      , .. }
            )

          | otherwise ->
            do sets_ $ \NonLinS { .. } ->
                 NonLinS { nonLinExprs = Map.delete x nonLinExprs
                         , nlKnown = trie_delete e nlKnown
                         , ..
                         }
               es <- mapM nonLinExprM (cryExprExprs e2)
               let e3 = cryRebuildExpr e2 es
               return (Updated (Just (x,e3)))



-- | Is the top-level operator a non-linear one.
isNonLinOp :: Expr -> Bool
isNonLinOp expr =
  case expr of
    K _   -> False
    Var _ -> False

    _ :+ _ -> False

    _ :- _ -> False

    x :* y ->
      case (x,y) of
        (K _, _)  -> False
        (_, K _)  -> False
        _         -> True

    Div _ y ->
      case y of
        K (Nat n) -> n == 0
        _         -> True

    Mod _ y ->
      case y of
        K (Nat n) -> n == 0
        _         -> True

    _ :^^ _       -> True

    Min _ _       -> False

    Max _ _       -> False

    Lg2 _         -> True

    Width _       -> True

    LenFromThen _ _ _ -> True -- See also comment on `LenFromThenTo`

    LenFromThenTo x y _ ->
      case (x,y) of
        (K _, K _) -> False
        _          -> True    -- Actually, as long as the difference bettwen
                              -- `x` and `y` is constant we'd be OK, but not
                              -- sure how to do that...

nlImplied :: Expr -> Name -> [Prop]
nlImplied expr x =
  map crySimplify $
  case expr of
    K (Nat n) :^^ e | n >= 2 -> [ Var x :>= one, Var x :>= e :+ one ]
    Mod _ e                  -> [ e     :>= Var x :+ one ]

    _                        -> []




nonLinPropM :: Prop -> NonLinM Prop
nonLinPropM prop =
  case prop of
    PFalse      -> return PFalse
    PTrue       -> return PTrue
    Not p       -> Not   `fmap` nonLinPropM p
    p :&& q     -> (:&&) `fmap` nonLinPropM p `ap` nonLinPropM q
    p :|| q     -> (:||) `fmap` nonLinPropM p `ap` nonLinPropM q
    Fin (Var _) -> return prop
    Fin _       -> unexpected
    x :==: y    -> (:==:) `fmap` nonLinExprM x `ap` nonLinExprM y
    x :>: y     -> (:>:)  `fmap` nonLinExprM x `ap` nonLinExprM y

    _ :== _     -> unexpected
    _ :>= _     -> unexpected
    _ :> _      -> unexpected

  where
  unexpected = panic "nonLinPropM" [ show (ppProp prop) ]



nonLinExprM :: Expr -> NonLinM Expr
nonLinExprM expr
  | isNonLinOp expr = nameExpr expr
  | otherwise = cryRebuildExpr expr `fmap` mapM nonLinExprM (cryExprExprs expr)



type NonLinM = StateT NonLinS Id

data NonLinS = NonLinS
  { nextName    :: !Int
  , nonLinExprs :: Subst
  , nlKnown     :: Trie Expr Name
  , nlTodo      :: [Prop]
  } deriving Show

nameExpr :: Expr -> NonLinM Expr
nameExpr e = sets $ \s ->
  case trie_lookup e (nlKnown s) of
    Just x -> (Var x, s)
    Nothing ->
      let x  = nextName s
          n  = SysName x
          s1 = NonLinS { nextName = 1 + x
                       , nonLinExprs = Map.insert n e (nonLinExprs s)
                       , nlKnown = trie_insert e n (nlKnown s)
                       , nlTodo = nlImplied e n ++ nlTodo s
                       }
      in (Var n, s1)


finishTodos :: NonLinM [Prop]
finishTodos =
  do s <- get
     case nlTodo s of
       [] -> return []
       p : ps ->
        do set s { nlTodo = ps }
           p'  <- nonLinPropM p
           ps' <- finishTodos
           return (p' : ps')





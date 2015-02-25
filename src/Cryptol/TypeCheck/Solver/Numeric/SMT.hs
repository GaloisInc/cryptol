{-# LANGUAGE Safe #-}
-- | Desugar into SMTLIB Terminology
module Cryptol.TypeCheck.Solver.Numeric.SMT
  ( desugarProp
  , smtName
  , smtFinName
  , ifPropToSmtLib
  , cryImproveModel
  ) where

import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.TypeCheck.Solver.Numeric.AST
import           Cryptol.TypeCheck.Solver.Numeric.Simplify(crySimplify)
import           Cryptol.Utils.Misc ( anyJust )
import           Cryptol.Utils.Panic ( panic )

import           Data.List ( partition, unfoldr )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set
import           SimpleSMT ( SExpr )
import qualified SimpleSMT as SMT
import           MonadLib


--------------------------------------------------------------------------------
-- Desugar to SMT
--------------------------------------------------------------------------------

-- XXX: Expanding the if-then-elses could make things large.
-- Perhaps keep them as first class things, in hope that the solver
-- can do something more clever with that?


-- | Assumes simplified, linear, finite, defined expressions.
desugarExpr :: Expr -> IfExpr Expr
desugarExpr expr =
  do es <- mapM desugarExpr (cryExprExprs expr)
     case (expr,es) of
       (Min {}, [x,y]) -> If (x :>: y) (return y) (return x)
       (Max {}, [x,y]) -> If (x :>: y) (return x) (return y)
       (LenFromThenTo {}, [ x@(K (Nat a)), K (Nat b), z ])
          | a > b -> If (z :>: x) (return zero)
                                  (return (Div (z :- x) step :+ one))
          | b < a -> If (x :>: z) (return zero)
                                  (return (Div (x :- z) step :+ one))

          where step = K (Nat (abs (a - b)))

       _ -> return (cryRebuildExpr expr es)


-- | Assumes simplified, linear, defined.
desugarProp :: Prop -> IfExpr Prop
desugarProp prop =
  case prop of
    PFalse      -> return PFalse
    PTrue       -> return PTrue
    Not p       -> Not   `fmap` desugarProp p
    p :&& q     -> (:&&) `fmap` desugarProp p `ap` desugarProp q
    p :|| q     -> (:||) `fmap` desugarProp p `ap` desugarProp q
    Fin (Var _) -> return prop
    x :==: y    -> (:==:) `fmap` desugarExpr x `ap` desugarExpr y
    x :>: y     -> (:>:)  `fmap` desugarExpr x `ap` desugarExpr y

    Fin _     -> unexpected
    _ :== _   -> unexpected
    _ :>= _   -> unexpected
    _ :> _    -> unexpected

  where
  unexpected = panic "desugarProp" [ show (ppProp prop) ]


ifPropToSmtLib :: IfExpr Prop -> SExpr
ifPropToSmtLib ifProp =
  case ifProp of
    Impossible -> SMT.bool False -- Sholdn't really matter
    Return p   -> propToSmtLib p
    If p q r   -> SMT.ite (propToSmtLib p) (ifPropToSmtLib q) (ifPropToSmtLib r)

propToSmtLib :: Prop -> SExpr
propToSmtLib prop =
  case prop of
    PFalse       -> SMT.bool False
    PTrue        -> SMT.bool True
    Not p        -> case p of
                      Fin _   -> SMT.not (propToSmtLib p)

                      -- It is IMPORTANT that the fin constraints are outside
                      -- the not.
                      x :>: y -> addFin $ SMT.geq (exprToSmtLib y)
                                                  (exprToSmtLib x)
                      _ -> unexpected


    p :&& q     -> SMT.and (propToSmtLib p) (propToSmtLib q)
    p :|| q     -> SMT.or  (propToSmtLib p) (propToSmtLib q)
    Fin (Var x) -> fin x

    {- For the linear constraints, if the term is finite, then all of
       its variables must have been finite.

       XXX: Adding the `fin` decls at the leaves leads to some duplication:
       We could add them just once for each conjunctoin of simple formulas,
       but I am not sure how much this matters.
    -}
    x :==: y    -> addFin $ SMT.eq (exprToSmtLib x) (exprToSmtLib y)
    x :>: y     -> addFin $ SMT.gt (exprToSmtLib x) (exprToSmtLib y)

    Fin _       -> unexpected
    _ :== _     -> unexpected
    _ :>= _     -> unexpected
    _ :> _      -> unexpected

  where
  unexpected = panic "propToSmtLib" [ show (ppProp prop) ]
  fin x      = SMT.const (smtFinName x)

  addFin e   = foldr (\x' e' -> SMT.and (fin x') e') e
                     (Set.toList (cryPropFVS prop))

exprToSmtLib :: Expr -> SExpr
exprToSmtLib expr =

  case expr of
    K (Nat n)           -> SMT.int n
    Var a               -> SMT.const (smtName a)
    x :+ y              -> SMT.add (exprToSmtLib x) (exprToSmtLib y)
    x :- y              -> SMT.sub (exprToSmtLib x) (exprToSmtLib y)
    x :* y              -> SMT.mul (exprToSmtLib x) (exprToSmtLib y)
    Div x y             -> SMT.div (exprToSmtLib x) (exprToSmtLib y)
    Mod x y             -> SMT.mod (exprToSmtLib x) (exprToSmtLib y)

    K Inf               -> unexpected
    _ :^^ _             -> unexpected
    Min {}              -> unexpected
    Max {}              -> unexpected
    Lg2 {}              -> unexpected
    Width {}            -> unexpected
    LenFromThen {}      -> unexpected
    LenFromThenTo {}    -> unexpected

  where
  unexpected = panic "exprToSmtLib" [ show (ppExpr expr) ]


-- | The name of a variable in the SMT translation.
smtName :: Name -> String
smtName = show . ppName

-- | The name of a boolean variable, representing `fin x`.
smtFinName :: Name -> String
smtFinName x = "fin_" ++ show (ppName x)





--------------------------------------------------------------------------------
-- Models
--------------------------------------------------------------------------------

-- | Get the value for the given variable.
-- Assumes that we are in a SAT state.
getVal :: SMT.Solver -> Name -> IO Expr
getVal s a =
  do yes <- isInf a
     if yes
       then return (K Inf)
       else do v <- SMT.getConst s (smtName a)
               case v of
                 SMT.Int x | x >= 0 -> return (K (Nat x))
                 _ -> panic "cryCheck.getVal" [ "Not a natural number", show v ]

  where
  isInf v = do yes <- SMT.getConst s (smtFinName v)
               case yes of
                 SMT.Bool ans -> return (not ans)
                 _            -> panic "cryCheck.isInf"
                                       [ "Not a boolean value", show yes ]


-- | Get the values for the given names.
getVals :: SMT.Solver -> [Name] -> IO (Map Name Expr)
getVals s xs =
  do es <- mapM (getVal s) xs
     return (Map.fromList (zip xs es))


-- | Convert a bunch of improving equations into an idempotent substitution.
-- Assumes that the equations don't have loops.
toSubst :: Map Name Expr -> Subst
toSubst m0 = last (m0 : unfoldr step m0)
  where step m = do m1 <- anyJust (apSubst m) m
                    return (m1,m1)


{- | Given a model, compute an improving substitution, implied by the model.
The entries in the substitution look like this:

  * @x = A@         variable @x@ must equal constant @A@

  * @x = y@         variable @x@ must equal variable @y@

  * @x = A * y + B@ (coming soon)
                    variable @x@ is a linear function of @y@,
                    @A@ and @B@ are natural numbers.
-}


cryImproveModel :: SMT.Solver -> Set Name -> Map Name Expr -> IO (Map Name Expr)
cryImproveModel solver uniVars m = toSubst `fmap` go Map.empty initialTodo
  where
  -- Process unification variables first.  That way, if we get `x = y`, we'd
  -- prefer `x` to be a unificaiton variabl.
  initialTodo    = uncurry (++) $ partition isUniVar $ Map.toList m
  isUniVar (x,_) = x `Set.member` uniVars


  go done [] = return done
  go done ((x,e) : rest) =

    -- x = K?
    do mbCounter <- cryMustEqualK solver (Map.keys m) x e
       case mbCounter of
         Nothing -> go (Map.insert x e done) rest
         Just ce -> goV ce done [] x e rest

  goV ce done todo x e ((y,e') : more)
    -- x = y?
    | e == e' = do yesK <- cryMustEqualV solver x y
                   if yesK then go (Map.insert x (Var y) done)
                                   (reverse todo ++ more)
                           else tryLR

    | otherwise = tryLR

    where
    next = goV ce done ((y,e'):todo) x e more

    tryLR =
      case ( x `Set.member` uniVars
           , e
           , e'
           , Map.lookup x ce
           , Map.lookup y ce
           ) of
        (True, K x1, K y1, Just (K x2), Just (K y2)) ->
           do mb <- cryCheckLinRel solver y x (y1,x1) (y2,x2)
              case mb of
                Just r  -> go (Map.insert x r done)
                              (reverse todo ++ more)
                Nothing -> next
        _ -> next


  goV _ done todo _ _ [] = go done (reverse todo)





-- | Try to prove the given expression.
checkUnsat :: SMT.Solver -> SExpr -> IO Bool
checkUnsat s e =
  do SMT.push s
     SMT.assert s e
     res <- SMT.check s
     SMT.pop s
     return (res == SMT.Unsat)


-- | Try to prove the given expression.
-- If we fail, we try to give a counter example.
-- If the answer is unknown, then we return an empty counter example.
getCounterExample :: SMT.Solver -> [Name] -> SExpr -> IO (Maybe (Map Name Expr))
getCounterExample s xs e =
  do SMT.push s
     SMT.assert s e
     res <- SMT.check s
     ans <- case res of
              SMT.Unsat   -> return Nothing
              SMT.Unknown -> return (Just Map.empty)
              SMT.Sat     -> Just `fmap` getVals s xs
     SMT.pop s
     return ans





-- | Is this the only possible value for the constant, under the current
-- assumptions.
-- Assumes that we are in a 'Sat' state.
-- Returns 'Nothing' if the variables must always match the given value.
-- Otherwise, we return a counter-example (which may be empty, if uniknown)
cryMustEqualK :: SMT.Solver -> [Name] ->
                 Name -> Expr -> IO (Maybe (Map Name Expr))
cryMustEqualK solver xs x expr =
  case expr of
    K Inf     -> getCounterExample solver xs (SMT.const (smtFinName x))
    K (Nat n) -> getCounterExample solver xs $
                 SMT.not $
                 SMT.and (SMT.const $ smtFinName x)
                         (SMT.eq (SMT.const (smtName x)) (SMT.int n))
    _ -> panic "cryMustEqualK" [ "Not a constant", show (ppExpr expr) ]



-- | Do these two variables need to always be the same, under the current
-- assumptions.
-- Assumes that we are in a 'Sat' state.
cryMustEqualV :: SMT.Solver -> Name -> Name -> IO Bool
cryMustEqualV solver x y =
     checkUnsat solver $
        SMT.not $
        SMT.or (SMT.not (fin x) `SMT.and` SMT.not (fin y))
               (fin x `SMT.and` fin y `SMT.and` SMT.eq (var x) (var y))

  where fin a = SMT.const (smtFinName a)
        var a = SMT.const (smtName a)


-- | Try to find a linear relation between the two variables, based
-- on two observed data points.
-- NOTE:  The variable being defined is the SECOND name.
cryCheckLinRel :: SMT.Solver ->
         {- x -} Name {- ^ Definition in terms of this variable. -} ->
         {- y -} Name {- ^ Define this variable. -} ->
                 (Nat',Nat') {- ^ Values in one model (x,y) -} ->
                 (Nat',Nat') {- ^ Values in antoher model (x,y) -} ->
                 IO (Maybe Expr)
cryCheckLinRel s x y p1 p2 =
  -- First, try to find a linear relation that holds in all finite cases.
  do SMT.push s
     SMT.assert s (isFin x)
     SMT.assert s (isFin y)
     ans <- case (p1,p2) of
              ((Nat x1, Nat y1), (Nat x2, Nat y2)) ->
                  checkLR x1 y1 x2 y2

              ((Inf,    Inf),    (Nat x2, Nat y2)) ->
                 mbGoOn (getFinPt x2) $ \(x1,y1) -> checkLR x1 y1 x2 y2

              ((Nat x1, Nat y1), (Inf,    Inf)) ->
                 mbGoOn (getFinPt x1) $ \(x2,y2) -> checkLR x1 y1 x2 y2

              _ -> return Nothing

     SMT.pop s

     -- Next, check the infinite cases: if @y = A * x + B@, then
     -- either both @x@ and @y@ must be infinite or they both must be finite.
     -- Note that we don't consider relations where A = 0: because they
     -- would be handled when we checked that @y@ is a constant.
     case ans of
       Nothing -> return Nothing
       Just e ->
         do SMT.push s
            SMT.assert s (SMT.not (SMT.eq (isFin x) (isFin y)))
            c <- SMT.check s
            SMT.pop s
            case c of
              SMT.Unsat -> return (Just e)
              _         -> return Nothing

  where
  isFin a = SMT.const (smtFinName a)

  checkLR x1 y1 x2 y2 =
    mbGoOn (return (linRel (x1,y1) (x2,y2))) $ \(a,b) ->
      do let expr = case a of
                      1 -> Var x :+ K (Nat b)
                      _ -> K (Nat a) :* Var x :+ K (Nat b)
         proved <- checkUnsat s $ propToSmtLib $ crySimplify
                                $ Not $ Var y :==: expr
         if not proved
            then return Nothing
            else return (Just expr)

  -- Try to get an example of another point, which is finite, and at
  -- different @x@ coordinate.
  getFinPt otherX =
    do SMT.push s
       SMT.assert s (SMT.not (SMT.eq (SMT.const (smtName x)) (SMT.int otherX)))
       smtAns <- SMT.check s
       ans <- case smtAns of
                SMT.Sat ->
                  do vX <- SMT.getConst s (smtName x)
                     vY <- SMT.getConst s (smtName y)
                     case (vX, vY) of
                       (SMT.Int vx, SMT.Int vy)
                          | vx >= 0 && vy >= 0 -> return (Just (vx,vy))
                       _ -> return Nothing
                _ -> return Nothing
       SMT.pop s
       return ans

  mbGoOn m k = do ans <- m
                  case ans of
                    Nothing -> return Nothing
                    Just a  -> k a

{- | Compute a linear relation through two concrete points.
Try to find a relation of the form `y = a * x + b`, where both `a` and `b`
are naturals.

y1 = A * x1 + B
y2 = A * x2 + B
(y2 - y1) = A * (x2 - x1)

A = (y2 - y1) / (x2 - x1)
B = y1 - A * x1
-}
linRel :: (Integer,Integer)       {- ^ First point -} ->
          (Integer,Integer)       {- ^ Second point -} ->
          Maybe (Integer,Integer) {- ^ (A,B) -}
linRel (x1,y1) (x2,y2) =
  do guard (x1 /= x2)
     let (a,r) = divMod (y2 - y1) (x2 - x1)
     guard (r == 0 && a > 0)    -- Not interested in A = 0
     let b = y1 - a * x1
     guard (b >= 0)
     return (a,b)



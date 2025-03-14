{-# LANGUAGE PatternGuards, MagicHash, MultiWayIf, TypeOperators #-}
module Cryptol.TypeCheck.Solver.Numeric
  ( cryIsEqual, cryIsNotEqual, cryIsGeq, cryIsPrime, primeTable
  ) where

import           Control.Applicative(Alternative(..))
import           Control.Monad (guard,mzero)
import qualified Control.Monad.Fail as Fail
import           Data.List (sortBy, groupBy, sort)
import           Data.MemoTrie

import Math.NumberTheory.Primes.Testing (isPrime)

import Cryptol.Utils.Patterns
import Cryptol.TypeCheck.Type hiding (tMul,tExp,tSub)
import Cryptol.TypeCheck.TypePat
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Interval
import Cryptol.TypeCheck.SimpType as Simp

{- Convention for comments:

  K1, K2 ...          Concrete constants
  s1, s2, t1, t2 ...  Arbitrary type expressions
  a, b, c ...         Type variables

-}


-- | Try to solve @t1 = t2@
cryIsEqual :: Ctxt -> Type -> Type -> Solved
cryIsEqual ctxt t1 t2 =
  matchDefault Unsolved $
        (pBin (==) t1 t2)
    <|> (aNat' t1 >>= tryEqK ctxt t2)
    <|> (aNat' t2 >>= tryEqK ctxt t1)
    <|> (aTVar t1 >>= tryEqVar t2)
    <|> (aTVar t2 >>= tryEqVar t1)
    <|> ( guard (t1 == t2) >> return (SolvedIf []))
    <|> tryEqMin t1 t2
    <|> tryEqMin t2 t1
    <|> tryEqMins t1 t2
    <|> tryEqMins t2 t1
    <|> tryEqMulConst ctxt (=#=) t1 t2
    <|> tryEqAddInf ctxt t1 t2
    <|> tryAddConst (=#=) t1 t2
    <|> tryCancelVar ctxt (=#=) t1 t2
    <|> tryLinearSolution t1 t2
    <|> tryLinearSolution t2 t1
    <|> tryEqExp t1 t2

-- | Try to solve @t1 /= t2@
cryIsNotEqual :: Ctxt -> Type -> Type -> Solved
cryIsNotEqual _i t1 t2 = matchDefault Unsolved (pBin (/=) t1 t2)

-- | Try to solve @t1 >= t2@
cryIsGeq :: Ctxt -> Type -> Type -> Solved
cryIsGeq i t1 t2 =
  matchDefault Unsolved $
        (pBin (>=) t1 t2)
    <|> (aNat' t1 >>= tryGeqKThan i t2)
    <|> (aNat' t2 >>= tryGeqThanK i t1)
    <|> (aTVar t2 >>= tryGeqThanVar i t1)
    <|> tryGeqThanSub i t1 t2
    <|> (geqByInterval i t1 t2)
    <|> (guard (t1 == t2) >> return (SolvedIf []))
    <|> tryAddConst (>==) t1 t2
    <|> tryCancelVar i (>==) t1 t2
    <|> tryMinIsGeq t1 t2
    <|> tryGeqExp i t1 t2
    <|> tryEqMulConst i (>==) t1 t2
    -- XXX: k >= width e
    -- XXX: width e >= k


  -- XXX: max t 10 >= 2 --> True
  -- XXX: max t 2 >= 10 --> a >= 10

{-# NOINLINE primeTable #-}
primeTable :: Integer :->: Bool
primeTable = trie isPrime

cryIsPrime :: Ctxt -> Type -> Solved
cryIsPrime _varInfo ty =
  case tNoUser ty of

    TCon (TC tc) []
      | TCNum n <- tc ->
          if untrie primeTable n then
            SolvedIf []
          else
            Unsolvable

      | TCInf <- tc -> Unsolvable

    _ -> Unsolved


-- | Try to solve something by evaluation.
pBin :: (Nat' -> Nat' -> Bool) -> Type -> Type -> Match Solved
pBin p t1 t2
  | Just _ <- tIsError t1 = pure Unsolvable
  | Just _ <- tIsError t2 = pure Unsolvable
  | otherwise = do x <- aNat' t1
                   y <- aNat' t2
                   return $ if p x y
                              then SolvedIf []
                              else Unsolvable


--------------------------------------------------------------------------------
-- GEQ

-- | Try to solve @K >= t@
tryGeqKThan :: Ctxt -> Type -> Nat' -> Match Solved
tryGeqKThan _ _ Inf = return (SolvedIf [])
tryGeqKThan _ ty (Nat n) =

  -- K1 >= K2 * t
  do (a,b) <- aMul ty
     m     <- aNat' a
     return $ SolvedIf
            $ case m of
                Inf   -> [ b =#= tZero ]
                Nat 0 -> []
                Nat k -> [ tNum (div n k) >== b ]

-- | Try to solve @t >= K@
tryGeqThanK :: Ctxt -> Type -> Nat' -> Match Solved
tryGeqThanK _ t Inf = return (SolvedIf [ t =#= tInf ])
tryGeqThanK _ t (Nat k) =

  -- K1 + t >= K2
  do (a,b) <- anAdd t
     n     <- aNat a
     return $ SolvedIf $ if n >= k
                            then []
                            else [ b >== tNum (k - n) ]
  -- XXX: K1 ^^ n >= K2


-- (K >= 2 && K^a >= K^b) => a >= b
tryGeqExp :: Ctxt -> Type -> Type -> Match Solved
tryGeqExp _ x y = 
      do  (k_1, a) <- (|^|) x
          n <- aNat k_1
          guard (n >= 2)
          (k_2, b) <- (|^|) y
          guard (k_1 == k_2)
          return $ SolvedIf [ a >== b ]


tryGeqThanSub :: Ctxt -> Type -> Type -> Match Solved
tryGeqThanSub ctxt x y =

  -- t1 >= t1 - t2
  (do (a,_) <- (|-|) y
      guard (x == a)
      return (SolvedIf []))
  <|> do
    (x1, x2) <- (|-|) x
    (y1, y2) <- (|-|) y
    -- (x - z) >= (y - z)  only if x >= y
    ((guard (x2 == y2) >> return (SolvedIf [x1 >== y1]))
     <|>
    -- (z - x) >= (z - y)  only if y >= x and fin z
     (guard (x1 == y1 && tIsFin ctxt x1) >> return (SolvedIf [y2 >== x2])))

tryGeqThanVar :: Ctxt -> Type -> TVar -> Match Solved
tryGeqThanVar _ctxt ty x =
  -- (t + a) >= a
  do (a,b) <- anAdd ty
     let check y = do x' <- aTVar y
                      guard (x == x')
                      return (SolvedIf [])
     check a <|> check b

-- | Try to prove GEQ by considering the known intervals for the given types.
geqByInterval :: Ctxt -> Type -> Type -> Match Solved
geqByInterval ctxt x y =
  let ix = typeInterval (intervals ctxt) x
      iy = typeInterval (intervals ctxt) y
  in case (iLower ix, iUpper iy) of
       (l,Just n) | l >= n -> return (SolvedIf [])
       _                   -> mzero

-- min K1 t >= K2 ~~> t >= K2, if K1 >= K2;  Err otherwise
tryMinIsGeq :: Type -> Type -> Match Solved
tryMinIsGeq t1 t2 =
  do (a,b) <- aMin t1
     k1    <- aNat a
     k2    <- aNat t2
     return $ if k1 >= k2
               then SolvedIf [ b >== t2 ]
               else Unsolvable

--------------------------------------------------------------------------------

-- | Cancel finite positive variables from both sides.
-- @(fin a, a >= 1) =>  a * t1 == a * t2 ~~~> t1 == t2@
-- @(fin a, a >= 1) =>  a * t1 >= a * t2 ~~~> t1 >= t2@
tryCancelVar :: Ctxt -> (Type -> Type -> Prop) -> Type -> Type -> Match Solved
tryCancelVar ctxt p t1 t2 =
  let lhs = preproc t1
      rhs = preproc t2
  in case check [] [] lhs rhs of
       Nothing -> Fail.fail "tryCancelVar"
       Just x  -> return x


  where
  check doneLHS doneRHS lhs@((a,mbA) : moreLHS) rhs@((b, mbB) : moreRHS) =
    do x <- mbA
       y <- mbB
       case compare x y of
         LT -> check (a : doneLHS) doneRHS moreLHS rhs
         EQ -> return $ SolvedIf [ p (term (doneLHS ++ map fst moreLHS))
                                     (term (doneRHS ++ map fst moreRHS)) ]
         GT -> check doneLHS (b : doneRHS) lhs moreRHS
  check _ _ _ _ = Nothing

  term xs = case xs of
              [] -> tNum (1::Int)
              _  -> foldr1 tMul xs

  preproc t = let fs = splitMul t []
              in sortBy cmpFact (zip fs (map cancelVar fs))

  splitMul t rest = case matchMaybe (aMul t) of
                      Just (a,b) -> splitMul a (splitMul b rest)
                      Nothing    -> t : rest

  cancelVar t = matchMaybe $ do x <- aTVar t
                                guard (iIsPosFin (tvarInterval (intervals ctxt) x))
                                return x

  -- cancellable variables go first, sorted alphabetically
  cmpFact (_,mbA) (_,mbB) =
    case (mbA,mbB) of
      (Just x, Just y)  -> compare x y
      (Just _, Nothing) -> LT
      (Nothing, Just _) -> GT
      _                 -> EQ



-- if (K >= 2) && K^a = K^b => a = b
tryEqExp :: Type -> Type -> Match Solved
tryEqExp x y = check x y <|> check y x
  where 
    check i j =
      do  
          (k_1, a) <- (|^|) i
          n <- aNat k_1
          guard (n >= 2)
          (k_2, b) <- (|^|) j
          guard (k_1 == k_2)
          return $ SolvedIf [ a =#= b ]
  
-- min t1 t2 = t1 ~> t1 <= t2
tryEqMin :: Type -> Type -> Match Solved
tryEqMin x y =
  do (a,b) <- aMin x
     let check m1 m2 = do guard (m1 == y)
                          return $ SolvedIf [ m2 >== m1 ]
     check a b <|> check b a


-- t1 == min (K + t1) t2 ~~> t1 == t2, if K >= 1
-- (also if (K + t1) is one term in a multi-way min)
tryEqMins :: Type -> Type -> Match Solved
tryEqMins x y =
  do (a, b) <- aMin y
     let ys = splitMin a ++ splitMin b
     let ys' = filter (not . isGt) ys
     let y' = if null ys' then tInf else foldr1 Simp.tMin ys'
     return $ if length ys' < length ys
              then SolvedIf [x =#= y']
              else Unsolved
  where
    splitMin :: Type -> [Type]
    splitMin ty =
      case matchMaybe (aMin ty) of
        Just (t1, t2) -> splitMin t1 ++ splitMin t2
        Nothing       -> [ty]

    isGt :: Type -> Bool
    isGt t =
      case matchMaybe (asAddK t) of
        Just (k, t') -> k > 0 && t' == x
        Nothing      -> False

    asAddK :: Type -> Match (Integer, Type)
    asAddK t =
      do (t1, t2) <- anAdd t
         k <- aNat t1
         return (k, t2)


tryEqVar :: Type -> TVar -> Match Solved
tryEqVar ty x =

  -- a = K + a --> x = inf
  (do (k,tv) <- matches ty (anAdd, aNat, aTVar)
      guard (tv == x && k >= 1)

      return $ SolvedIf [ TVar x =#= tInf ]
  )
  <|>

  -- a = min (K + a) t --> a = t
  (do (l,r) <- aMin ty
      let check this other =
            do (k,x') <- matches this (anAdd, aNat', aTVar)
               guard (x == x' && k >= Nat 1)
               return $ SolvedIf [ TVar x =#= other ]
      check l r <|> check r l
  )
  <|>
  -- a = K + min t a
  (do (k,(l,r)) <- matches ty (anAdd, aNat, aMin)
      guard (k >= 1)
      let check a b = do x' <- aTVar a
                         guard (x' == x)
                         return (SolvedIf [ TVar x =#= tAdd (tNum k) b ])
      check l r <|> check r l
  )







-- e.g., 10 = t
tryEqK :: Ctxt -> Type -> Nat' -> Match Solved
tryEqK ctxt ty lk =

  -- (t1 + t2 = inf, fin t1) ~~~> t2 = inf
  do guard (lk == Inf)
     (a,b) <- anAdd ty
     let check x y = do guard (iIsFin (typeInterval (intervals ctxt) x))
                        return $ SolvedIf [ y =#= tInf ]
     check a b <|> check b a
  <|>

  -- (K1 + t = K2, K2 >= K1) ~~~> t = (K2 - K1)
  do (rk, b) <- matches ty (anAdd, aNat', __)
     return $
       case nSub lk rk of
         -- NOTE: (Inf - Inf) shouldn't be possible
         Nothing -> Unsolvable

         Just r -> SolvedIf [ b =#= tNat' r ]
  <|>

  -- (lk = t - rk) ~~> t = lk + rk
  do (t,rk) <- matches ty ((|-|) , __, aNat')
     return (SolvedIf [ t =#= tNat' (nAdd lk rk) ])

  <|>
  do (rk, b) <- matches ty (aMul, aNat', __)
     return $
       case (lk,rk) of
         -- Inf * t = Inf ~~~>  t >= 1
         (Inf,Inf)    -> SolvedIf [ b >== tOne ]

         -- K * t = Inf ~~~> t = Inf
         (Inf,Nat _)  -> SolvedIf [ b =#= tInf ]

         -- Inf * t = 0 ~~~> t = 0
         (Nat 0, Inf) -> SolvedIf [ b =#= tZero ]

         -- Inf * t = K ~~~> ERR      (K /= 0)
         (Nat _k, Inf) -> Unsolvable

         (Nat lk', Nat rk')
           -- 0 * t = K2 ~~> K2 = 0
           | rk' == 0 -> SolvedIf [ tNat' lk =#= tZero ]
              -- shouldn't happen, as `0 * t = t` should have been simplified

           -- K1 * t = K2 ~~> t = K2/K1
           | (q,0) <- divMod lk' rk' -> SolvedIf [ b =#= tNum q ]
           | otherwise -> Unsolvable

  <|>
  -- K1 == K2 ^^ t    ~~> t = logBase K2 K1
  do (rk, b) <- matches ty ((|^|), aNat, __)
     return $ case lk of
                Inf | rk > 1 -> SolvedIf [ b =#= tInf ]
                Nat n | Just (a,True) <- genLog n rk -> SolvedIf [ b =#= tNum a]
                _ -> Unsolvable

  -- XXX: Min, Max, etx
  -- 2  = min (10,y)  --> y = 2
  -- 2  = min (2,y)   --> y >= 2
  -- 10 = min (2,y)   --> impossible


-- | K1 * t1 + K2 * t2 + ... = K3 * t3 + K4 * t4 + ...
tryEqMulConst :: Ctxt -> (Type -> Type -> Prop) -> Type -> Type -> Match Solved
tryEqMulConst ctxt comp l r =
  do (lc,ls) <- matchLinear l
     (rc,rs) <- matchLinear r
     let d = foldr1 gcd (lc : rc : map fst (ls ++ rs))
     let (ls', rs') = if tIsFin ctxt l && tIsFin ctxt r then
           cancelCommon [] [] (sort $ groupCommon ls) (sort $ groupCommon rs)
           else (ls,rs)
     guard (d > 1 || length ls' < length ls || length rs' < length rs)
     return (SolvedIf [comp (build d lc ls') (build d rc rs')])
  where
  build d k ts   = foldr (tAdd' d) (cancel d k) ts
  buildS d (k,t) = tMul (cancel d k) t
  cancel d x     = tNum (div x d)
  tAdd' d (k, t) x = tAdd  (buildS d (k, t)) x
  
  -- group common terms
  -- a * x + ... + b * x ~> (a + b) * x + ...
  groupCommon ts = map (collapseSame 0) $ groupBy (\(_,t1) (_, t2) -> t1 == t2) ts
  collapseSame k ts = case ts of
    [(k1,t)] -> (k + k1, t)
    ((k1,_):rest) -> collapseSame (k + k1) rest
    [] -> error "empty list"
  
  -- cancel out common terms from both sides
  -- assumes ls and rs are sorted
  -- 2x + y = 4x + z
  -- ~> y = 2x + z
  cancelCommon accL accR [] rs = (accL, accR ++ rs)
  cancelCommon accL accR ls [] = (accL ++ ls, accR)
  cancelCommon accL accR ((kl, l1):ls) ((kr, r1):rs) =
    case compare l1 r1 of
      LT -> cancelCommon ((kl, l1):accL) accR ls ((kr, r1):rs)
      GT -> cancelCommon accL ((kr,r1):accR) ((kl, l1):ls) rs
      EQ -> case compare kl kr of
        GT -> cancelCommon ((kl - kr,l1):accL) accR ls rs
        LT -> cancelCommon accL ((kr - kl,r1):accR) ls rs
        EQ -> cancelCommon accL accR ls rs

tIsFin :: Ctxt -> Type -> Bool
tIsFin ctxt t = iIsFin (typeInterval (intervals ctxt) t)

-- | @(t1 + t2 = Inf, fin t1)  ~~> t2 = Inf@
tryEqAddInf :: Ctxt -> Type -> Type -> Match Solved
tryEqAddInf ctxt l r = check l r <|> check r l
  where

  -- check for x = a + b /\ x = inf
  check x y =
    do (x1,x2) <- anAdd x
       aInf y

       let x1Fin = iIsFin (typeInterval (intervals ctxt) x1)
       let x2Fin = iIsFin (typeInterval (intervals ctxt) x2)

       return $!
         if | x1Fin ->
              SolvedIf [ x2 =#= y ]

            | x2Fin ->
              SolvedIf [ x1 =#= y ]

            | otherwise ->
              Unsolved



-- | Check for addition of constants to both sides of a relation.
--  @((K1 + K2) + t1) `R` (K1 + t2)  ~~>   (K2 + t1) `R` t2@
--
-- This relies on the fact that constants are floated left during
-- simplification.
tryAddConst :: (Type -> Type -> Prop) -> Type -> Type -> Match Solved
tryAddConst rel l r =
  do (x1,x2) <- anAdd l
     (y1,y2) <- anAdd r

     k1 <- aNat x1
     k2 <- aNat y1

     if k1 > k2
        then return (SolvedIf [ tAdd (tNum (k1 - k2)) x2 `rel` y2 ])
        else return (SolvedIf [ x2 `rel` tAdd (tNum (k2 - k1)) y2 ])


-- | Check for situations where a unification variable is involved in
--   a sum of terms not containing additional unification variables,
--   and replace it with a solution and an inequality.
--   @s1 = ?a + s2 ~~> (?a = s1 - s2, s1 >= s2)@
tryLinearSolution :: Type -> Type -> Match Solved
tryLinearSolution s1 t =
  do (a,xs) <- matchLinearUnifier t
     guard (noFreeVariables s1)

     -- NB: matchLinearUnifier only matches if xs is nonempty
     let s2 = foldr1 Simp.tAdd xs
     return (SolvedIf [ TVar a =#= (Simp.tSub s1 s2), s1 >== s2 ])


-- | Match a sum of the form @(s1 + ... + ?a + ... sn)@ where
--   @s1@ through @sn@ do not contain any free variables.
--
--   Note: a successful match should only occur if @s1 ... sn@ is
--   not empty.
matchLinearUnifier :: Pat Type (TVar,[Type])
matchLinearUnifier = go []
 where
  go xs t =
    -- Case where a free variable occurs at the end of a sequence of additions.
    -- NB: match fails if @xs@ is empty
    do v <- aFreeTVar t
       guard (not . null $ xs)
       return (v, xs)
    <|>
    -- Next symbol is an addition
    do (x, y) <- anAdd t

        -- Case where a free variable occurs in the middle of an expression
       (do v <- aFreeTVar x
           guard (noFreeVariables y)
           return (v, reverse (y:xs))

        <|>
         -- Non-free-variable recursive case
        do guard (noFreeVariables x)
           go (x:xs) y)


-- | Is this a sum of products, where the products have constant coefficients?
matchLinear :: Pat Type (Integer, [(Integer,Type)])
matchLinear = go (0, [])
  where

  go (c,ts) t =
    do n <- aNat t
       return (n + c, ts)
    <|>
    do (x,y) <- aMul t
       n     <- aNat x
       return (c, (n,y) : ts)
    <|>
    do (l,r) <- anAdd t
       (c',ts') <- go (c,ts) l
       go (c',ts') r
    <|>
    --     l - r 
    -- ~~> l - (c + (i * t1 + h * t2 ...))
    -- ~~> l + (-c) + (-i)*t1 + (-h)*t2 ...
    do (l,r) <- (|-|) t
       (cL,tsL) <- go (c,ts) l
       (cR, tsR) <- go (0,[]) r
       let tsR' = map (\(x,y) -> (x * (-1), y)) tsR
       return $ (cL - cR, tsL ++ tsR')
    <|>
    -- for constants K, n: K^(n + a) ~> K^n * K^a
    do (t_base, t_exp) <- (|^|) t
       m <- aNat t_base
       guard (m >= 2)
       t_sum <- anAdd t_exp
       matchSwap t_sum $ \(l, r) ->
        do n <- aNat l
           guard (n > 0)
           return (c, (m ^ n, tExp t_base r) : ts)
    <|> return (c, (1,t) : ts)




-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}
module Cryptol.TypeCheck.Solver.CrySAT
  (debug
  , Prop(..)
  , Expr(..)
  , PropSet
  , noProps
  , assert
  , checkSat
  , Result(..)
  , InfNat(..)
  , Name
  , toName
  , fromName
  ) where

import qualified Data.Integer.SAT as SAT
import           Data.Set(Set)
import qualified Data.Set as Set
import           Data.Either (partitionEithers)
import           MonadLib
import           Control.Applicative

import           Cryptol.Utils.Panic

infixr 2 :||
infixr 3 :&&
infix  4 :==, :>, :>=
infixl 6 :+, :-
infixl 7 :*


data Name = UserName Int | SysName Int
            deriving (Show,Eq,Ord)

toName :: Int -> Name
toName = UserName

fromName :: Name -> Maybe Int
fromName (UserName x) = Just x
fromName (SysName _)  = Nothing


exportName :: Name -> SAT.Name
exportName n = SAT.toName $ case n of
                              UserName i -> 2 * i
                              SysName i  -> 2 * i + 1

satVar :: Name -> SAT.Expr
satVar = SAT.Var . exportName

importName :: Int -> Name
importName x = case divMod x 2 of
                 (q,r) | r == 0     -> UserName q
                       | otherwise  -> SysName q

satCheckSat :: SAT.PropSet -> Maybe [ (Name,Integer) ]
satCheckSat =  fmap (map imp) . SAT.checkSat
  where imp (x,v) = (importName x, v)


data Prop = Fin Expr
          | Expr :== Expr | Expr :/= Expr
          | Expr :>= Expr | Expr :> Expr
          | Prop :&& Prop | Prop :|| Prop
          | Not Prop
            deriving Show

data Expr = K InfNat
          | Var Name
          | Expr :+ Expr
          | Expr :- Expr
          | Expr :* Expr
          | Div Expr Expr
          | Mod Expr Expr
          | Expr :^^ Expr
          | Min Expr Expr
          | Max Expr Expr
          | Lg2 Expr
          | Width Expr
          | LenFromThen   Expr Expr Expr
          | LenFromThenTo Expr Expr Expr
            deriving Show

debug :: PropSet -> [S]
debug (PS m) = runId $ findAll m

newtype PropSet = PS (ChoiceT Id S)

noProps :: PropSet
noProps = PS $ return S { finVars   = Set.empty
                        , infVars   = Set.empty
                        , linear    = SAT.noProps
                        , nonLin    = []
                        , waitVars  = Set.empty
                        , changes   = False
                        , nextVar   = 0
                        }

assert :: Prop -> PropSet -> PropSet
assert p (PS m) =
  PS $ do s <- m
          (_,s1) <- runStateT s
                  $ unFM
                  $ cvt p >> checkConsistent
          return s1

  where
  cvt (p1 :&& p2) = cvt p1 `mkAnd` cvt p2
  cvt (p1 :|| p2) = cvt p1 `mkOr`  cvt p2
  cvt (Not p1)    = cvt (mkNot p1)
  cvt (Fin t)     = cryDefined t  `mkAnd` cryIsFin t
  cvt (t1 :== t2) = cryDefined t1 `mkAnd` cryDefined t2 `mkAnd` cryIsEq  t1 t2
  cvt (t1 :/= t2) = cryDefined t1 `mkAnd` cryDefined t2 `mkAnd` cryIsNeq t1 t2
  cvt (t1 :>= t2) = cryDefined t1 `mkAnd` cryDefined t2 `mkAnd` cryIsGeq t1 t2
  cvt (t1 :>  t2) = cryDefined t1 `mkAnd` cryDefined t2 `mkAnd` cryIsGt  t1 t2

  mkNot q = case q of
              p1 :&& p2 -> mkNot p1 :|| mkNot p2
              p1 :|| p2 -> mkNot p1 :&& mkNot p2
              Not p1    -> p1
              Fin e     -> e  :== K Inf
              t1 :== t2 -> t1 :/= t2
              t1 :/= t2 -> t1 :== t2
              t1 :>= t2 -> t2 :> t1
              t1 :>  t2 -> t2 :>= t1


data InfNat = Nat Integer | Inf
              deriving (Eq,Ord,Show)

data Result = Sat [(Int,InfNat)]
            | Unsat
            | Unknown
              deriving Show

checkSat :: PropSet -> Result
checkSat (PS ch) =
  runId $
  do mb <- runChoiceT ch
     return $ case mb of
                Nothing -> Unsat
                Just (s, more) ->
                  case getModel s of
                    Just m  -> Sat m
                    Nothing -> case checkSat (PS more) of
                                 Unsat -> Unknown
                                 x     -> x

getModel :: S -> Maybe [(Int,InfNat)]
getModel s =
  do let ps = linear s
     m  <- satCheckSat ps
     let exact = [ satVar x SAT.:== SAT.K v | (x,v) <- m ]
     m1 <- satCheckSat $ foldr SAT.assert SAT.noProps
                       $ exact ++
                         [ satVar x SAT.:== cvt m nl | (x,nl) <- nonLin s ]
     return [ (x,v) | (UserName x, v)
                          <- [ (x,Inf)  | x <- Set.toList (infVars s) ] ++
                             [ (x,Nat v) | (x,v) <- m1 ] ]

  where
  lkp m x = case lookup x m of
              Nothing -> 0
              Just n  -> n
  cvt m nl =
    case nl of
      NLDiv e x  -> SAT.Div e (lkp m x)
      NLMod e x  -> SAT.Mod e (lkp m x)
      NLExp x y  -> SAT.K $ lkp m x ^ lkp m y
      NLExpL k y -> SAT.K $ k ^ lkp m y
      NLExpR x k -> SAT.K $ lkp m x ^ k
      NLMul x y  -> SAT.K $ lkp m x * lkp m y
      NLLg2 x    -> SAT.K $ nLg2 (lkp m x)



--------------------------------------------------------------------------------

data NonLin = NLDiv SAT.Expr Name
            | NLMod SAT.Expr Name
            | NLExp Name Name
            | NLExpL Integer Name
            | NLExpR Name Integer
            | NLMul Name Name
            | NLLg2 Name
              deriving Show

setNL :: Name -> Integer -> (Name,NonLin) -> Either (Name,NonLin) SAT.Prop
setNL x n (v, nl) = case it of
                      Left nl1 -> Left (x,nl1)
                      Right e  -> Right (satVar v SAT.:== e)
  where
  it = case nl of
         NLDiv e y  | x == y            -> Right $ SAT.Div e n
         NLMod e y  | x == y            -> Right $ SAT.Mod e n
         NLMul y z  | y == z && x == y  -> Right $ SAT.K $ n * n
                    | x == y            -> Right $ n SAT.:* satVar z
                    | x == z            -> Right $ n SAT.:* satVar y
         NLExp y z  | y == z && x == y  -> Right $ SAT.K $ n ^ n
                    | x == y            -> Left  $ NLExpL n z
                    | x == z            -> Left  $ NLExpR y n
         NLExpL k z | x == z            -> Right $ SAT.K $ k ^ n
         NLExpR y k | x == y            -> Right $ SAT.K $ n ^ k
         NLLg2 y    | x == y            -> Right $ SAT.K $ nLg2 n
         _                              -> Left nl


data S = S
  { finVars   :: Set Name     -- all of these are ordinary finite vars
  , infVars   :: Set Name     -- these vars are all equal to Inf (XXX: subst?)
  , linear    :: SAT.PropSet  -- linear constraints
  , nonLin    :: [(Name,NonLin)] -- non-linear (delayed) constraints
  , waitVars  :: Set Name     -- waiting for improvements to these
                              -- improvements here may turn non-lin into lin
                              -- INV: these are a subset of finVars
  , changes   :: Bool         -- temp: did something improve last time?
                              -- if so we should restart.
  , nextVar   :: !Int         -- source of new variables
  }

newtype FM a = FM { unFM :: StateT S (ChoiceT Id) a }

instance Functor FM where
  fmap f (FM m) = FM (fmap f m)

instance Applicative FM where
  pure x          = FM (pure x)
  FM mf <*> FM mx = FM (mf <*> mx)

instance Alternative FM where
  empty = mzero
  (<|>) = mplus

instance Monad FM where
  return x        = FM (return x)
  FM mf >>= k     = FM (mf >>= unFM . k)

instance MonadPlus FM where
  mzero = FM mzero
  mplus (FM m1) (FM m2) = FM (mplus m1 m2)


noChanges :: F
noChanges = FM $ sets_ $ \s -> s { changes = False }

addLin :: SAT.Prop -> F
addLin p = FM $ sets_ $ \s -> s { linear = SAT.assert p (linear s)
                                , changes = True }


checkConsistent :: F
checkConsistent =
  do s <- FM get
     when (changes s) $
       case satCheckSat (linear s) of
         Nothing -> mzero
         Just m  ->
          do noChanges
             mapM_ tryImprove [ (x,v) | (x,v) <- m, x `Set.member` waitVars s ]
             checkConsistent

tryImprove :: (Name,Integer) -> F
tryImprove (x,n) =
  do s <- FM get
     case satCheckSat (SAT.assert (satVar x SAT.:/= SAT.K n) (linear s)) of
       Nothing -> doImprove x n
       Just _  -> return ()

doImprove :: Name -> Integer -> F
doImprove x n =
  do resumed <- FM $ sets $ \s ->
       let (stay, go) = partitionEithers $ map (setNL x n) (nonLin s)
       in (go, s { nonLin = stay, waitVars = Set.delete x (waitVars s) })
     mapM_ addLin resumed


getLin :: FM SAT.PropSet
getLin = FM $ linear `fmap` get

newName :: FM Name
newName = FM $ sets $ \s -> let x = nextVar s
                            in (SysName x, s { nextVar = x + 1 })

addNonLin :: NonLin -> FM SAT.Expr
addNonLin nl =
  do x <- newName
     FM $ sets_ $ \s -> s { nonLin = (x,nl) : nonLin s }
     isFin x
     return $ satVar x


type F = FM ()

mkAnd :: F -> F -> F
mkAnd f1 f2 = f1 >> f2

mkOr  :: F -> F -> F
mkOr f1 f2 = f1 `mplus` f2

tt :: F
tt = return ()

ff :: F
ff = mzero

isEq :: Expr -> Expr -> F
isEq t1 t2 = addLin =<< ((SAT.:==) <$> mkLin t1 <*> mkLin t2)

isGt :: Expr -> Expr -> F
isGt t1 t2 = addLin =<< ((SAT.:>) <$> mkLin t1 <*> mkLin t2)

isFin :: Name -> F
isFin x = do FM $ do s <- get
                     guard (Set.notMember x (infVars s))
                     set s { finVars = Set.insert x (finVars s) }
             addLin (satVar x SAT.:>= SAT.K 0)

isInf :: Name -> F
isInf x = FM $ do s <- get
                  guard (Set.notMember x (finVars s))
                  set s { infVars = Set.insert x (infVars s) }



--------------------------------------------------------------------------------


cryIsEq :: Expr -> Expr -> F
cryIsEq t1 t2 = (cryIsInf t1 `mkAnd` cryIsInf t2) `mkOr`
                (cryIsFin t1 `mkAnd` cryIsFin t2 `mkAnd` isEq t1 t2)

cryIsNeq :: Expr -> Expr -> F
cryIsNeq t1 t2 = cryIsGt t1 t2 `mkOr` cryIsGt t2 t1

cryIsGt :: Expr -> Expr -> F
cryIsGt t1 t2 = (cryIsInf t1 `mkAnd` cryIsFin t2) `mkOr`
                (cryIsFin t1 `mkAnd` cryIsFin t2  `mkAnd` isGt t1 t2)

cryIsGeq :: Expr -> Expr -> F
cryIsGeq t1 t2 = cryIsEq t1 t2 `mkOr` cryIsGt t1 t2

cryIsDifferent :: Expr -> Expr -> F
cryIsDifferent t1 t2 = cryIsGt t1 t2 `mkOr` cryIsGt t2 t1


{- XXX: Are we being a bit too strict here?
Some oprtations may be defined even if one of their arguments
is not.  For example, perhaps the following should not be rejected:
inf + undefined -> inf
0 - undefined   -> 0
0 * undefined   -> 0
mod undefined 1 -> 0
1 ^ undefined   -> 1
undefined ^ 0   -> 1`
min 0 undefined -> 0
max inf undefined -> inf
-}
cryDefined :: Expr -> F
cryDefined ty =
  case ty of
    K _        -> tt
    Var _      -> tt
    t1 :+ t2  -> cryDefined t1 `mkAnd` cryDefined t2
    t1 :- t2  -> cryDefined t1 `mkAnd` cryDefined t2 `mkAnd`
                 cryIsFin t2   `mkAnd` cryIsGeq t1 t2
    t1 :* t2  -> cryDefined t1 `mkAnd` cryDefined t2
    Div t1 t2  -> cryDefined t1 `mkAnd` cryDefined t2 `mkAnd`
                  cryIsFin t1   `mkAnd` cryIsGt t2 (K $ Nat 0)
    Mod t1 t2  -> cryDefined t1 `mkAnd` cryDefined t2 `mkAnd`
                  cryIsFin t1   `mkAnd` cryIsGt t2 (K $ Nat 0)

    t1 :^^ t2  -> cryDefined t1 `mkAnd` cryDefined t2
    Min t1 t2  -> cryDefined t1 `mkAnd` cryDefined t2
    Max t1 t2  -> cryDefined t1 `mkAnd` cryDefined t2
    Lg2 t1     -> cryDefined t1
    Width t1   -> cryDefined t1
    LenFromThen t1 t2 t3 ->
      cryDefined t1 `mkAnd` cryDefined t2 `mkAnd`
      cryDefined t3 `mkAnd` cryIsFin t1   `mkAnd`
      cryIsFin t2   `mkAnd` cryIsFin t3  `mkAnd`
      cryIsDifferent t1 t2
    LenFromThenTo t1 t2 t3 ->
      cryDefined t1 `mkAnd` cryDefined t2 `mkAnd`
      cryDefined t3 `mkAnd` cryIsFin t1   `mkAnd`
      cryIsFin t2   `mkAnd` cryIsFin t3  `mkAnd`
      cryIsDifferent t1 t2


-- Assuming a defined input.
cryIsInf :: Expr -> F
cryIsInf ty =
  case ty of
    K Inf               -> tt
    K (Nat _)           -> ff
    Var x               -> isInf x
    t1 :+ t2            -> cryIsInf t1 `mkOr` cryIsInf t2
    t1 :- _             -> cryIsInf t1
    t1 :* t2            -> (cryIsInf t1 `mkAnd` cryIsGt t2 (K $ Nat 0))`mkOr`
                           (cryIsInf t2 `mkAnd` cryIsGt t1 (K $ Nat 0))
    Div t1 _            -> cryIsInf t1
    Mod _  _            -> ff
    t1 :^^ t2           -> (cryIsInf t1 `mkAnd` cryIsGt t2 (K $ Nat 0))`mkOr`
                           (cryIsInf t2 `mkAnd` cryIsGt t1 (K $ Nat 1))
    Min t1 t2           -> cryIsInf t1  `mkAnd` cryIsInf t2
    Max t1 t2           -> cryIsInf t1 `mkOr` cryIsInf t2
    Lg2 t1              -> cryIsInf t1
    Width t1            -> cryIsInf t1
    LenFromThen _ _ _   -> ff
    LenFromThenTo _ _ _ -> ff


-- Assuming a defined input.
cryIsFin :: Expr -> F
cryIsFin ty =
  case ty of
    K Inf         -> ff
    K (Nat _)     -> tt
    Var x         -> isFin x
    t1 :+ t2      -> cryIsFin t1 `mkAnd` cryIsFin t2
    t1 :- _       -> cryIsFin t1
    t1 :* t2      -> (cryIsFin t1 `mkAnd` cryIsFin t2) `mkOr`
                      cryIsEq t1 (K $ Nat 0)       `mkOr`
                      cryIsEq t2 (K $ Nat 0)

    Div t1 _      -> cryIsFin t1
    Mod _ _       -> tt
    t1 :^^ t2     -> (cryIsFin t1 `mkAnd` cryIsFin t2) `mkOr`
                      cryIsEq t1 (K $ Nat 0)            `mkOr`
                      cryIsEq t1 (K $ Nat 1)            `mkOr`
                      cryIsEq t2 (K $ Nat 0)

    Min t1 t2     -> (cryIsFin t1 `mkAnd` cryIsGeq t2 t1) `mkOr`
                     (cryIsFin t2 `mkAnd` cryIsGeq t1 t2)

    Max t1 t2     -> cryIsFin t1 `mkAnd` cryIsFin t2
    Lg2 t1        -> cryIsFin t1
    Width t1      -> cryIsFin t1
    LenFromThen  _ _ _   -> tt
    LenFromThenTo  _ _ _ -> tt

-- eliminate Inf terms from finite values
cryNoInf :: Expr -> FM Expr
cryNoInf ty =
  case ty of
    K Inf :+ _   -> mzero
    _ :+ K Inf   -> mzero

    K Inf :- _   -> mzero
    _ :- K Inf   -> mzero

    K Inf :* t2  -> cryIsEq t2 (K $ Nat 0) >> return (K $ Nat 0)
    t1 :* K Inf  -> cryIsEq t1 (K $ Nat 0) >> return (K $ Nat 0)

    Div (K Inf) _    -> mzero
    Div _ (K Inf)    -> return $ K $ Nat 0

    Mod (K Inf) _    -> mzero
    Mod t1 (K Inf)   -> cryNoInf t1

    K Inf :^^ t2   -> cryIsEq t2 (K $ Nat 0) >> return (K $ Nat 1)
    t1 :^^ K Inf   -> msum [ cryIsEq t1 (K $ Nat 0) >> return (K $ Nat 0)
                           , cryIsEq t1 (K $ Nat 1) >> return (K $ Nat 1)
                           ]

    Min (K Inf) t2   -> cryNoInf t2
    Min t1 (K Inf)   -> cryNoInf t1

    Max (K Inf) _    -> mzero
    Max _ (K Inf)    -> mzero

    Lg2 (K Inf)      -> mzero

    Width (K Inf)    -> mzero

    LenFromThen (K Inf) _ _   -> mzero
    LenFromThen _ (K Inf) _   -> mzero
    LenFromThen _ _ (K Inf)   -> mzero

    LenFromThenTo (K Inf) _ _ -> mzero
    LenFromThenTo _ (K Inf) _ -> mzero
    LenFromThenTo _ _ (K Inf) -> mzero

    K Inf                    -> mzero

    _                        -> return ty


-- Assumes a finite, and defined input.
mkLin :: Expr -> FM SAT.Expr
mkLin ty0 =
  cryNoInf ty0 >>= \ty ->
  case ty of
    K Inf                  -> panic "Cryptol.TypeCheck.Solver.CrySAT.mkLin"
                                [ "K Inf after cryNoInf" ]
    K (Nat n)              -> return (SAT.K n)
    Var x                  -> isFin x >> return (satVar x)
    t1 :+ t2               -> (SAT.:+)            <$> mkLin t1 <*> mkLin t2
    t1 :- t2               -> (SAT.:-)            <$> mkLin t1 <*> mkLin t2
    t1 :* t2               -> join $ mkMul        <$> mkLin t1 <*> mkLin t2
    Div t1 t2              -> join $ mkDiv        <$> mkLin t1 <*> mkLin t2
    Mod t1 t2              -> join $ mkMod        <$> mkLin t1 <*> mkLin t2
    t1 :^^ t2              -> join $ mkExp        <$> mkLin t1 <*> mkLin t2
    Min t1 t2              -> mkMin               <$> mkLin t1 <*> mkLin t2
    Max t1 t2              -> mkMax               <$> mkLin t1 <*> mkLin t2
    Lg2 t1                 -> join $ mkLg2        <$> mkLin t1
    Width t1               -> join $ mkWidth       <$> mkLin t1
    LenFromThen t1 t2 t3   -> join $ mkLenFromThen <$> mkLin t1
                                                   <*> mkLin t2
                                                   <*> mkLin t3
    LenFromThenTo t1 t2 t3 -> join $ mkLenFromThenTo <$> mkLin t1
                                                     <*> mkLin t2
                                                     <*> mkLin t3
  where
  mkMin t1 t2 = SAT.If (t1 SAT.:< t2) t1 t2
  mkMax t1 t2 = SAT.If (t1 SAT.:< t2) t2 t1

  mkMul t1 t2 =
    do mb <- toConst t1
       case mb of
         Just n -> return (n SAT.:* t2)
         Nothing ->
            do mb1 <- toConst t2
               case mb1 of
                 Just n  -> return (n SAT.:* t1)
                 Nothing -> do x <- toVar t1
                               y <- toVar t2
                               addNonLin (NLMul x y)

  mkDiv t1 t2 =
    do mb <- toConst t2
       case mb of
         Just n  -> return (SAT.Div t1 n)
         Nothing -> do x <- toVar t2
                       addNonLin (NLDiv t1 x)

  mkMod t1 t2 =
    do mb <- toConst t2
       case mb of
         Just n  -> return (SAT.Mod t1 n)
         Nothing -> do x <- toVar t2
                       addNonLin (NLMod t1 x)

  mkLg2 t1 =
    do mb <- toConst t1
       case mb of
         Just n   -> return $ SAT.K $ nLg2 n
         Nothing  -> do x <- toVar t1
                        addNonLin (NLLg2 x)

  mkWidth t1 = mkLg2 (SAT.K 1 SAT.:+ t1)

  mkExp t1 t2 =
    do mb <- toConst t1
       case mb of
         Just n ->
           do mb1 <- toConst t2
              case mb1 of
                Just m  -> return $ SAT.K $ n ^ m
                Nothing -> do y <- toVar t2
                              addNonLin (NLExpL n y)
         Nothing -> do x <- toVar t1
                       y <- toVar t2
                       addNonLin (NLExp x y)



  -- derived
  mkLenFromThen x y w =
    do upTo <- msum [ do addLin (y SAT.:> x)
                         w1 <- mkExp (SAT.K 2) w
                         return (w1 SAT.:- SAT.K 1)
                    , do addLin (x SAT.:> y)
                         return (SAT.K 0)
                    ]
       mkLenFromThenTo x y upTo

  mkLenFromThenTo x y z =
    msum [ do addLin (x SAT.:> y)   -- going down
              msum [ addLin (z SAT.:> x)  >> return (SAT.K 0)
                   , addLin (z SAT.:== x) >> return (SAT.K 1)
                   , do addLin (z SAT.:< x)
                        t <- mkDiv (x SAT.:- z) (x SAT.:- y)
                        return (SAT.K 1 SAT.:+ t)
                   ]

         , do addLin (x SAT.:< y)   -- going up
              msum [ addLin (z SAT.:< x)  >> return (SAT.K 0)
                   , addLin (z SAT.:== x) >> return (SAT.K 1)
                   , do addLin (z SAT.:> x)
                        t <- mkDiv (z SAT.:- x) (y SAT.:- x)
                        return (SAT.K 1 SAT.:+ t)
                   ]

         ]

toConst :: SAT.Expr -> FM (Maybe Integer)
toConst (SAT.K n) = return (Just n)
toConst t = do l <- getLin
               case SAT.getExprRange t l of
                 Nothing -> return Nothing
                 Just vs -> msum $ map (return . Just) vs

toVar :: SAT.Expr -> FM Name
toVar (SAT.Var x) | Just n <- SAT.fromName x = return $ importName n
toVar e       = do x <- newName
                   addLin (satVar x SAT.:== e)
                   FM $ sets_ $ \s -> s { waitVars = Set.insert x (waitVars s) }
                   return x

--------------------------------------------------------------------------------

-- | Rounds up.
-- @lg2 x = y@, iff @y@ is the smallest number such that @x <= 2 ^ y@
nLg2 :: Integer -> Integer
nLg2 0  = 0
nLg2 n  = case genLog n 2 of
            Just (x,exact) | exact     -> x
                           | otherwise -> x + 1
            Nothing -> panic "Cryptol.TypeCheck.Solver.CrySAT.nLg2"
                         [ "genLog returned Nothing" ]



--------------------------------------------------------------------------------

-- | Compute the logarithm of a number in the given base, rounded down to the
-- closest integer.  The boolean indicates if we the result is exact
-- (i.e., True means no rounding happened, False means we rounded down).
-- The logarithm base is the second argument.
genLog :: Integer -> Integer -> Maybe (Integer, Bool)
genLog x 0    = if x == 1 then Just (0, True) else Nothing
genLog _ 1    = Nothing
genLog 0 _    = Nothing
genLog x base = Just (exactLoop 0 x)
  where
  exactLoop s i
    | i == 1     = (s,True)
    | i < base   = (s,False)
    | otherwise  =
        let s1 = s + 1
        in s1 `seq` case divMod i base of
                      (j,r)
                        | r == 0    -> exactLoop s1 j
                        | otherwise -> (underLoop s1 j, False)

  underLoop s i
    | i < base  = s
    | otherwise = let s1 = s + 1 in s1 `seq` underLoop s1 (div i base)




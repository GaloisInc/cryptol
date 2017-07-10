{-# Language FlexibleInstances #-}
module Cryptol.TypeCheck.Solver.SMT (proveImp,checkUnsolvable) where

import           SimpleSMT (SExpr)
import qualified SimpleSMT as SMT
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Maybe(catMaybes)
import           Data.List(partition)
import           Control.Monad(msum,zipWithM)

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.CrySAT
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.TypePat hiding ((~>),(~~>))
import Cryptol.Utils.Panic


-- | Returns goals that were not proved
proveImp :: Solver -> [Prop] -> [Goal] -> IO [Goal]
proveImp sol ps gs0 =
  debugBlock sol "PROVE IMP" $
  do let s = rawSolver sol
     let (gs,rest) = partition (isNumeric . goal) gs0
         numAsmp   = filter isNumeric ps
         vs        = Set.toList (fvs (numAsmp, map goal gs))
     tvs <- debugBlock sol "VARIABLES" $
       do SMT.push s
          Map.fromList <$> zipWithM (declareVar s) [ 0 .. ] vs
     debugBlock sol "ASSUMPTIONS" $
       mapM_ (assume s tvs) numAsmp
     gs' <- mapM (prove sol tvs) gs
     SMT.pop s
     return (catMaybes gs' ++ rest)

-- | Check if the given goals are known to be unsolvable.
checkUnsolvable :: Solver -> [Goal] -> IO Bool
checkUnsolvable sol gs0 =
  debugBlock sol "CHECK UNSOLVABLE" $
  do let s  = rawSolver sol
         ps = filter isNumeric (map goal gs0)
         vs = Set.toList (fvs ps)
     tvs <- debugBlock sol "VARIABLES" $
       do SMT.push s
          Map.fromList <$> zipWithM (declareVar s) [ 0 .. ] vs
     ans <- unsolvable sol tvs ps
     SMT.pop s
     return ans

--------------------------------------------------------------------------------

declareVar :: SMT.Solver -> Int -> TVar -> IO (TVar, SExpr)
declareVar s x v = do let name = (if isFreeTV v then "fv" else "kv") ++ show x
                      e <- SMT.declare s name cryInfNat
                      SMT.assert s (SMT.fun "cryVar" [ e ])
                      return (v,e)

assume :: SMT.Solver -> TVars -> Prop -> IO ()
assume s tvs p = SMT.assert s (SMT.fun "cryAssume" [ toSMT tvs p ])

prove :: Solver -> TVars -> Goal -> IO (Maybe Goal)
prove sol tvs g =
  debugBlock sol "PROVE" $
  do let s = rawSolver sol
     SMT.push s
     SMT.assert s (SMT.fun "cryProve" [ toSMT tvs (goal g) ])
     res <- SMT.check s
     SMT.pop s
     case res of
       SMT.Unsat -> return Nothing
       _         -> return (Just g)


-- | Check if some numeric goals are known to be unsolvable.
unsolvable :: Solver -> TVars -> [Prop] -> IO Bool
unsolvable sol tvs ps =
  debugBlock sol "UNSOLVABLE" $
  do let s = rawSolver sol
     SMT.push s
     mapM_ (assume s tvs) ps
     res <- SMT.check s
     SMT.pop s
     case res of
       SMT.Unsat -> return True
       _         -> return False



--------------------------------------------------------------------------------

isNumeric :: Prop -> Bool
isNumeric ty = matchDefault False
             $ msum [ is (|=|), is (|>=|), is aFin, is aTrue, andNum ty ]
  where
  andNum t = anAdd t >>= \(x,y) -> return (isNumeric x && isNumeric y)
  is f = f ty >> return True

--------------------------------------------------------------------------------

type TVars = Map TVar SExpr

cryInfNat :: SExpr
cryInfNat = SMT.const "InfNat"


toSMT :: TVars -> Type -> SExpr
toSMT tvs ty = matchDefault (panic "toSMT" [ "Unexpected type", show ty ])
  $ msum $ map (\f -> f tvs ty)
  [ aInf            ~> "cryInf"
  , aNat            ~> "cryNat"

  , aFin            ~> "cryFin"
  , (|=|)           ~> "cryEq"
  , (|>=|)          ~> "cryGeq"
  , aAnd            ~> "cryAnd"
  , aTrue           ~> "cryTrue"

  , anAdd           ~> "cryAdd"
  , (|-|)           ~> "crySub"
  , aMul            ~> "cryMul"
  , (|^|)           ~> "cryExp"
  , (|/|)           ~> "cryDiv"
  , (|%|)           ~> "cryMod"
  , aMin            ~> "cryMin"
  , aMax            ~> "cryMax"
  , aWidth          ~> "cryWidth"
  , aLenFromThen    ~> "cryLenFromThen"
  , aLenFromThenTo  ~> "cryLenFromThenTo"

  , aTVar           ~> "(unused)"
  ]

--------------------------------------------------------------------------------

(~>) :: Mk a => (Type -> Match a) -> String -> TVars -> Type -> Match SExpr
(m ~> f) tvs t = m t >>= \a -> return (mk tvs f a)

class Mk t where
  mk :: TVars -> String -> t -> SExpr

instance Mk () where
  mk _ f _ = SMT.const f

instance Mk Integer where
  mk _ f x = SMT.fun f [ SMT.int x ]

instance Mk TVar where
  mk tvs _ x = tvs Map.! x

instance Mk Type where
  mk tvs f x = SMT.fun f [toSMT tvs x]

instance Mk (Type,Type) where
  mk tvs f (x,y) = SMT.fun f [ toSMT tvs x, toSMT tvs y]

instance Mk (Type,Type,Type) where
  mk tvs f (x,y,z) = SMT.fun f [ toSMT tvs x, toSMT tvs y, toSMT tvs z ]

--------------------------------------------------------------------------------






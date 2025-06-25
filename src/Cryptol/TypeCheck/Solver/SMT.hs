-- |
-- Module      :  Cryptol.TypeCheck.Solver.SMT
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}

module Cryptol.TypeCheck.Solver.SMT
  ( -- * Setup
    Solver
  , SolverConfig
  , withSolver
  , startSolver
  , stopSolver
  , isNumeric
  , resetSolver

    -- * Debugging
  , debugBlock
  , debugLog

    -- * Proving stuff
  , proveImp
  , checkUnsolvable
  , tryGetModel
  , shrinkModel

    -- * Lower level interactions
  , inNewFrame, TVars, declareVars, assume, unsolvable
  , push, pop
  ) where

import           SimpleSMT (SExpr)
import qualified SimpleSMT as SMT
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Maybe(catMaybes,isJust)
import           Data.List(partition)
import           Control.Exception
import           Control.Monad(msum,zipWithM,void)
import           Data.Char(isSpace)
import           Text.Read(readMaybe)
import           System.IO(IOMode(..), hClose, openFile)
import qualified System.IO.Strict as StrictIO
import           System.FilePath((</>))
import           System.Directory(doesFileExist)

import Cryptol.Prelude(cryptolTcContents)
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.TypeCheck.TypePat hiding ((~>),(~~>))
import Cryptol.TypeCheck.Subst(Subst)
import Cryptol.Utils.Panic
import Cryptol.Utils.PP ( Doc, pp )




-- | An SMT solver packed with a logger for debugging.
data Solver = Solver
  { solver    :: SMT.Solver
    -- ^ The actual solver

  , logger    :: SMT.Logger
    -- ^ For debugging
  }

setupSolver :: Solver -> SolverConfig -> IO ()
setupSolver s cfg = do
  _ <- SMT.setOptionMaybe (solver s) ":global-decls" "false"
  SMT.setLogic (solver s) "ALL"
  loadTcPrelude s (solverPreludePath cfg)

-- | Start a fresh solver instance
startSolver :: IO () -> SolverConfig -> IO Solver
startSolver onExit sCfg =
   do let smtFileEnabled = isJust (solverSmtFile sCfg)
      (logger, mbLoggerCloseHdl) <-
        -- There are two scenarios under which we want to explicitly log SMT
        -- solver interactions:
        --
        -- 1. The user wants to debug-print interactions with the `tcDebug`
        --    option
        -- 2. The user wants to write interactions to the `tcSmtFile` option
        --
        -- We enable logging if either one is true.
        if (solverVerbose sCfg) > 0 || smtFileEnabled
        then case solverSmtFile sCfg of
               Nothing ->
                 do logger <- SMT.newLogger 0
                    pure (logger, Nothing)
               Just file ->
                 do loggerHdl <- openFile file WriteMode
                    logger <- SMT.newLoggerWithHandle loggerHdl 0
                    pure (logger, Just (hClose loggerHdl))
        else pure (quietLogger, Nothing)
      let smtDbg = if (solverVerbose sCfg) > 1 || smtFileEnabled
                   then Just logger
                   else Nothing
      solver <- SMT.newSolverWithConfig
                  (SMT.defaultConfig (solverPath sCfg) (solverArgs sCfg))
                    { SMT.solverOnExit =
                        Just $ \_exitCode ->
                        do onExit
                           sequence_ mbLoggerCloseHdl
                    , SMT.solverLogger =
                        maybe SMT.noSolverLogger SMT.smtSolverLogger smtDbg
                    }
      let sol = Solver solver logger
      setupSolver sol sCfg
      return sol

  where
  quietLogger = SMT.Logger { SMT.logMessage = \_ -> return ()
                           , SMT.logLevel   = return 0
                           , SMT.logSetLevel= \_ -> return ()
                           , SMT.logTab     = return ()
                           , SMT.logUntab   = return ()
                           }

-- | Shut down a solver instance
stopSolver :: Solver -> IO ()
stopSolver s = void $ SMT.stop (solver s)

resetSolver :: Solver -> SolverConfig -> IO ()
resetSolver s sCfg = do
  _ <- SMT.simpleCommand (solver s) ["reset"]
  setupSolver s sCfg

-- | Execute a computation with a fresh solver instance.
withSolver :: IO () -> SolverConfig -> (Solver -> IO a) -> IO a
withSolver onExit cfg = bracket (startSolver onExit cfg) stopSolver

-- | Load the definitions used for type checking.
loadTcPrelude :: Solver -> [FilePath] {- ^ Search in this paths -} -> IO ()
loadTcPrelude s [] = loadString s cryptolTcContents
loadTcPrelude s (p : ps) =
  do let file = p </> "CryptolTC.z3"
     yes <- doesFileExist file
     if yes then loadFile s file
            else loadTcPrelude s ps


loadFile :: Solver -> FilePath -> IO ()
loadFile s file = loadString s =<< StrictIO.readFile file

loadString :: Solver -> String -> IO ()
loadString s str = go (dropComments str)
  where
  go txt
    | all isSpace txt = return ()
    | otherwise =
      case SMT.readSExpr txt of
        Just (e,rest) -> SMT.command (solver s) e >> go rest
        Nothing       -> panic "loadFile" [ "Failed to parse SMT file."
                                          , txt
                                          ]

  dropComments = unlines . map dropComment . lines
  dropComment xs = case break (== ';') xs of
                     (as,_:_) -> as
                     _ -> xs




--------------------------------------------------------------------------------
-- Debugging


debugBlock :: Solver -> String -> IO a -> IO a
debugBlock s@Solver { .. } name m =
  do debugLog s (";;; " ++ name)
     SMT.logTab logger
     a <- m
     SMT.logUntab logger
     return a

class DebugLog t where
  debugLog :: Solver -> t -> IO ()

  debugLogList :: Solver -> [t] -> IO ()
  debugLogList s ts = case ts of
                        [] -> debugLog s "(none)"
                        _  -> mapM_ (debugLog s) ts

instance DebugLog Char where
  debugLog s x     = SMT.logMessage (logger s) (show x)
  debugLogList s x = SMT.logMessage (logger s) x

instance DebugLog a => DebugLog [a] where
  debugLog = debugLogList

instance DebugLog a => DebugLog (Maybe a) where
  debugLog s x = case x of
                   Nothing -> debugLog s "(nothing)"
                   Just a  -> debugLog s a

instance DebugLog Doc where
  debugLog s x = debugLog s (show x)

instance DebugLog Type where
  debugLog s x = debugLog s (pp x)

instance DebugLog Goal where
  debugLog s x = debugLog s (goal x)

instance DebugLog Subst where
  debugLog s x = debugLog s (pp x)
--------------------------------------------------------------------------------


-- | Returns goals that were not proved
proveImp :: Solver -> [Prop] -> [Goal] -> IO [Goal]
proveImp sol ps gs0 =
  debugBlock sol "PROVE IMP" $
  do let gs1       = concatMap flatGoal gs0
         (gs,rest) = partition (isNumeric . goal) gs1
         numAsmp   = filter isNumeric (concatMap pSplitAnd ps)
         vs        = Set.toList (fvs (numAsmp, map goal gs))
     tvs <- debugBlock sol "VARIABLES" $
       do SMT.push (solver sol)
          Map.fromList <$> zipWithM (declareVar sol) [ 0 .. ] vs
     debugBlock sol "ASSUMPTIONS" $
       mapM_ (assume sol tvs) numAsmp
     gs' <- mapM (prove sol tvs) gs
     SMT.pop (solver sol)
     return (catMaybes gs' ++ rest)

-- | Check if the given goals are known to be unsolvable.
checkUnsolvable :: Solver -> [Goal] -> IO Bool
checkUnsolvable sol gs0 =
  debugBlock sol "CHECK UNSOLVABLE" $
  do let ps = filter isNumeric
            $ map goal
            $ concatMap flatGoal gs0
         vs = Set.toList (fvs ps)
     tvs <- debugBlock sol "VARIABLES" $
       do push sol
          Map.fromList <$> zipWithM (declareVar sol) [ 0 .. ] vs
     ans <- unsolvable sol tvs ps
     pop sol
     return ans

tryGetModel :: Solver -> [TVar] -> [Prop] -> IO (Maybe [(TVar,Nat')])
tryGetModel sol as ps =
  debugBlock sol "TRY GET MODEL" $
  do push sol
     tvs <- Map.fromList <$> zipWithM (declareVar sol) [ 0 .. ] as
     mapM_ (assume sol tvs) ps
     sat <- SMT.check (solver sol)
     su <- case sat of
             SMT.Sat ->
               case as of
                 [] -> return (Just [])
                 _ -> do res <- SMT.getExprs (solver sol) (Map.elems tvs)
                         let parse x = do e <- Map.lookup x tvs
                                          t <- parseNum =<< lookup e res
                                          return (x, t)
                         return (mapM parse as)
             _ -> return Nothing
     pop sol
     return su

  where
  parseNum a
    | SMT.Other s <- a
    , SMT.List [con,val,isFin,isErr] <- s
    , SMT.Atom "mk-infnat" <- con
    , SMT.Atom "false"     <- isErr
    , SMT.Atom fin         <- isFin
    , SMT.Atom v           <- val
    , Just n               <- readMaybe v
    = Just (if fin == "false" then Inf else Nat n)

  parseNum _ = Nothing

shrinkModel :: Solver -> [TVar] -> [Prop] -> [(TVar,Nat')] -> IO [(TVar,Nat')]
shrinkModel sol as ps0 mdl = go [] ps0 mdl
  where
  go done ps ((x,Nat k) : more) =
    do k1 <- shrink1 ps x k
       go ((x,Nat k1) : done) ((tNum k1 >== TVar x) : ps) more

  go done ps ((x,i) : more) = go ((x,i) : done) ps more
  go done _ [] = return done

  shrink1 ps x k
    | k == 0 = return 0
    | otherwise =
      do let k1 = div k 2
             p1 = tNum k1 >== TVar x
         mb <- tryGetModel sol as (p1 : ps)
         case mb of
           Nothing     -> return k
           Just newMdl ->
             case lookup x newMdl of
               Just (Nat k2) -> shrink1 ps x k2
               _ -> panic "shrink" ["model is missing variable", show x]



--------------------------------------------------------------------------------

push :: Solver -> IO ()
push sol = SMT.push (solver sol)

pop :: Solver -> IO ()
pop sol = SMT.pop (solver sol)

inNewFrame :: Solver -> IO a -> IO a
inNewFrame sol m =
  do push sol
     a <- m
     pop sol
     pure a


declareVar :: Solver -> Int -> TVar -> IO (TVar, SExpr)
declareVar s x v =
  do let name = (if isFreeTV v then "fv" else "kv") ++ show x
     e <- SMT.declare (solver s) name cryInfNat
     SMT.assert (solver s) (SMT.fun "cryVar" [ e ])
     return (v,e)


declareVars :: Solver -> [TVar] -> IO TVars
declareVars sol vs =
  Map.fromList <$> zipWithM (declareVar sol) [ 0 .. ]
                                             [ v | v <- vs, kindOf v == KNum ]

assume :: Solver -> TVars -> Prop -> IO ()
assume s tvs p = SMT.assert (solver s) (SMT.fun "cryAssume" [ toSMT tvs p ])

prove :: Solver -> TVars -> Goal -> IO (Maybe Goal)
prove sol tvs g =
  debugBlock sol "PROVE" $
  do let s = solver sol
     push sol
     SMT.assert s (SMT.fun "cryProve" [ toSMT tvs (goal g) ])
     res <- SMT.check s
     pop sol
     case res of
       SMT.Unsat -> return Nothing
       _         -> return (Just g)


-- | Check if some numeric goals are known to be unsolvable.
unsolvable :: Solver -> TVars -> [Prop] -> IO Bool
unsolvable sol tvs ps =
  debugBlock sol "UNSOLVABLE" $
  do SMT.push (solver sol)
     mapM_ (assume sol tvs) ps
     res <- SMT.check (solver sol)
     SMT.pop (solver sol)
     case res of
       SMT.Unsat -> return True
       _         -> return False



--------------------------------------------------------------------------------

-- | Split up the 'And' in a goal
flatGoal :: Goal -> [Goal]
flatGoal g = [ g { goal = p } | p <- pSplitAnd (goal g) ]


-- | Assumes no 'And'
isNumeric :: Prop -> Bool
isNumeric ty = matchDefault False $ msum [ is (|=|), is (|/=|), is (|>=|)
                                         , is aFin, is aPrime ]
  where
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
  , aPrime          ~> "cryPrime"
  , (|=|)           ~> "cryEq"
  , (|/=|)          ~> "cryNeq"
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
  , aCeilDiv        ~> "cryCeilDiv"
  , aCeilMod        ~> "cryCeilMod"
  , aLenFromThenTo  ~> "cryLenFromThenTo"

  , anError KNum    ~> "cryErr"
  , anError KProp   ~> "cryErrProp"

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

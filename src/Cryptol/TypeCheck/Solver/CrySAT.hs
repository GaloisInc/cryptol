{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.TypeCheck.Solver.CrySAT
  ( Name, toName, fromName
  , Prop(..), Expr(..), IfExpr(..)
  , cryAnds, cryOrs
  , crySimplify, crySimplified
  , cryDefined, cryDefinedProp
  , ppProp, ppPropPrec, ppExpr, ppExprPrec, ppIfExpr, ppName
  ) where

import           Cryptol.TypeCheck.Solver.Numeric.AST
import           Cryptol.TypeCheck.Solver.Numeric.Defined
import           Cryptol.TypeCheck.Solver.Numeric.Simplify
import           Cryptol.TypeCheck.Solver.Numeric.NonLin
import           Cryptol.TypeCheck.Solver.Numeric.SMT
import           Cryptol.Utils.Panic ( panic )

import           Control.Monad ( unless )
import           Data.List ( intersperse )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.IORef ( IORef, newIORef, readIORef, modifyIORef' )

import           Text.PrettyPrint
import           SimpleSMT ( SExpr )
import qualified SimpleSMT as SMT


test1 :: IO ()
test1 =
  do (res,mb) <- withSolver $ \s ->
                          cryCheck s $ prepareProp (a :== Max a (a :+ one))
     print res
     case mb of
       Just (m,eqs) ->
          do print $ vcat [ ppName x <+> text "=" <+> ppExpr e
                                      | (x,e) <- Map.toList m ]
             putStrLn "improvements:"
             print $ vcat [ ppName x <+> text "=" <+> ppExpr e
                                      | (x,e) <- Map.toList eqs ]
       Nothing -> return ()
  where
  a : b : c : d : _ = map (Var . toName) [ 0 .. ]

test :: IO ()
test =
  do writeFile "out"
      $ unlines
      $ intersperse (replicate 80 '-')
      $ map (show . ppProp)
      $ crySimpSteps
      $ Min (a :* b) (inf :* (inf :* (c :+ d))) :== a
  where
  a : b : c : d : _ = map (Var . toName) [ 0 .. ]

  _rest = Div a b
         : Mod a (b :* inf)
         : Min (a :* b) (inf :* (inf :* (c :+ d)))
         : []



data SimpS a = SimpS
  { simpsTodo       :: [ (a, Prop) ]
  , simpsDefined    :: [ (a, SMTProp) ]       -- (ct, exp-prop)
  , simpsNotDefined :: [ (a, Prop, SMTProp) ] -- (ct, prop, exp-defined-prop)
  , simpsChanges    :: !Bool
  }

-- | Check that a bunch of constraints are all defined.
-- If some are not, we return them on the 'Left'.
-- Otherwise, we return the exported props on the 'Right'.
checkDefined :: (a -> Prop) -> [a] -> IO (Either [a] [(a,SMTProp)])
checkDefined export props0 = withSolver $ \s ->
  go s False [] [] [ (p, q, prepareProp (cryDefinedProp q))
                                          | p <- props0, let q = export p ]

  where
  -- Everything is defined: keep going.
  go _ _    isDef []       [] = return (Right isDef)

  -- We have possibly non-defined, but we also added a new fact: go again.
  go s True isDef isNotDef [] = go s False isDef [] isNotDef

  -- We have possibly non-defined, and nothing changed: report error.
  go s False _ isNotDef [] = return (Left [ ct | (ct,_,_) <- isNotDef ])

  -- Process one constraint.
  go s ch isDef isNotDef ((ct,p,q) : more) =
    do proved <- prove s q
       if proved then do let r = prepareProp p
                         assert s r
                         go s True ((ct,r) : isDef) isNotDef  more
                 else go s ch isDef ((ct,p,q) : isNotDef) more






--------------------------------------------------------------------------------

data SMTProp = SMTProp
  { smtpVars        :: Set Name
  , smtpLinPart     :: SExpr
  , smtpNonLinPart  :: [(Name,Expr)]
  }

-- | Prepare a property for export to an SMT solver.
prepareProp :: Prop -> SMTProp
prepareProp prop0 = SMTProp
  { smtpVars       = cryPropFVS linProp
  , smtpLinPart    = ifPropToSmtLib (desugarProp linProp)
  , smtpNonLinPart = nonLinEs
  }
  where
  prop1               = crySimplify prop0
  (nonLinEs, linProp) = nonLinProp prop1


-- | An SMT solver, and some info about declared variables.
data Solver = Solver
  { solver    :: SMT.Solver
  , declared  :: IORef VarInfo
  }

-- | Keeps track of what variables we've already declared.
data VarInfo = VarInfo
  { curScope    :: Scope
  , otherScopes :: [Scope]
  }

data Scope = Scope
  { scopeNames    :: [Name]         -- ^ Variables declared in this scope
  , scopeAsmps    :: [(Name,Expr)]  -- ^ Non-linear assumptions.
  }

scopeEmpty :: Scope
scopeEmpty = Scope { scopeNames = [], scopeAsmps = [] }

scopeElem :: Name -> Scope -> Bool
scopeElem x Scope { .. } = x `elem` scopeNames

scopeInsert :: Name -> Scope -> Scope
scopeInsert x Scope { .. } = Scope { scopeNames = x : scopeNames, .. }

scopeAssert :: [(Name,Expr)] -> Scope -> Scope
scopeAssert as Scope { .. } = Scope { scopeAsmps = as ++ scopeAsmps }


-- | No scopes.
viEmpty :: VarInfo
viEmpty = VarInfo { curScope = scopeEmpty, otherScopes = [] }

-- | Check if a name is any of the scopes.
viElem :: Name -> VarInfo -> Bool
viElem x VarInfo { .. } = any (x `scopeElem`) (curScope : otherScopes)

-- | Add a name to a scope.
viInsert :: Name -> VarInfo -> VarInfo
viInsert x VarInfo { .. } = VarInfo { curScope = scopeInsert x curScope, .. }

-- | Add some non-linear assertions to the current scope.
viAssert :: [(Name,Expr)] -> VarInfo -> VarInfo
viAssert as VarInfo { .. } = VarInfo { curScope = scopeAssert as curScope, .. }

-- | Enter a scope.
viPush :: VarInfo -> VarInfo
viPush VarInfo { .. } = VarInfo { curScope = scopeEmpty
                                , otherScopes = curScope : otherScopes }

-- | Exit a scope.
viPop :: VarInfo -> VarInfo
viPop VarInfo { .. } = case otherScopes of
                         curScope : otherScopes -> VarInfo { .. }
                         _ -> panic "viPop" ["no more scopes"]

-- | Execute a computation with a fresh solver instance.
withSolver :: (Solver -> IO a) -> IO a
withSolver k =
  do l      <- SMT.newLogger
     solver <- SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] (Just l)
     SMT.setLogic solver "QF_LIA"
     declared <- newIORef viEmpty
     a <- k Solver { .. }
     _ <- SMT.stop solver
     return a

-- | Execute a computation in a new solver scope.
withScope :: Solver -> IO a -> IO a
withScope Solver { .. } k =
  do SMT.push solver
     modifyIORef' declared viPush
     a <- k
     modifyIORef' declared viPop
     SMT.pop solver
     return a

-- | Declare a variable.
declareVar :: Solver -> Name -> IO ()
declareVar Solver { .. } a =
  do done <- fmap (a `viElem`) (readIORef declared)
     unless done $
       do e  <- SMT.declare solver (smtName a)    SMT.tInt
          _  <- SMT.declare solver (smtFinName a) SMT.tBool
          SMT.assert solver(SMT.geq e (SMT.int 0))
          modifyIORef' declared (viInsert a)

-- | Add an assertion to the current context.
assert :: Solver -> SMTProp -> IO ()
assert Solver { .. } SMTProp { .. } =
  do SMT.assert solver smtpLinPart
     modifyIORef' declared (viAssert smtpNonLinPart)


-- | Try to prove a property.  The result is 'True' when we are sure that
-- the property holds, and 'False' otherwise.  In other words, getting `False`
-- *does not* mean that the proposition does not hold.
prove :: Solver -> SMTProp -> IO Bool
prove s@(Solver { .. }) SMTProp { .. } =
  withScope s $
  do mapM_ (declareVar s) (Set.toList smtpVars)
     SMT.assert solver (SMT.not smtpLinPart)
     res <- SMT.check solver
     case res of
       SMT.Unsat   -> return True
       SMT.Unknown -> return False  -- We are not sure
       SMT.Sat     -> return False
        -- XXX: If the answer is Sat, it is possible that this is a
        -- a fake example, as we need to evaluate the nonLinear constraints.
        -- If they are all satisfied, then we have a genuine counter example.
        -- Otherwise, we could look for another one...





-- | Assumes well-defined.
-- XXX: NONLIN, ETC
cryCheck :: Solver -> SMTProp -> IO ( SMT.Result
                                    , Maybe (Map Name Expr, Map Name Expr)
                                    )
cryCheck s SMTProp { .. } =
  do mapM_ (declareVar s) (Set.toList smtpVars)
     SMT.assert (solver s) smtpLinPart
     res <- SMT.check (solver s)
     case res of
       SMT.Sat -> do m   <- cryGetModel (solver s) (Set.toList smtpVars)
                     eqs <- cryImproveModel (solver s) m
                     return (res, Just (m,eqs))
       _       -> return (res, Nothing)

--------------------------------------------------------------------------------




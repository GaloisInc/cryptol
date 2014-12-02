{-# LANGUAGE Safe #-}
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

import           Data.List(intersperse)
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map

import           Text.PrettyPrint
import qualified SimpleSMT as SMT


test1 :: IO ()
test1 =
  do l <- SMT.newLogger
     p <- SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] (Just l)
     SMT.setLogic p "QF_LIA"
     (res,mb) <- cryCheck p (a :== Max a (a :+ one))
     print res
     case mb of
       Just (m,eqs) ->
          do print $ vcat [ ppName x <+> text "=" <+> ppExpr e
                                      | (x,e) <- Map.toList m ]
             putStrLn "improvements:"
             print $ vcat [ ppName x <+> text "=" <+> ppExpr e
                                      | (x,e) <- Map.toList eqs ]
       Nothing -> return ()
     print =<< SMT.stop p

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











--------------------------------------------------------------------------------


-- | Assumes well-defined.
cryCheck :: SMT.Solver -> Prop -> IO ( SMT.Result
                                     , Maybe (Map Name Expr, Map Name Expr)
                                     )
cryCheck p prop0 =
  do let prop1 = crySimplify prop0
         (nonLinEs, linProp) = nonLinProp prop1
         as = cryPropFVS linProp

         smtProp = desugarProp linProp
     mapM_ declareVar (Set.toList as)
     SMT.assert p (ifPropToSmtLib smtProp)
     res <- SMT.check p
     case res of
       SMT.Sat -> do m   <- cryGetModel p (Set.toList as)
                     eqs <- cryImproveModel p m
                     return (res, Just (m,eqs))
       _       -> return (res, Nothing)
{-
  in vcat $ smtDeclareVars as
          : text (SMT.showsSExpr (ifPropToSmtLib smtProp) "")
          : text "where"
          : [ ppName x <+> text "=" <+> ppExpr e | (x,e) <- nonLinEs ]
-}
  where
  declareVar a = do e  <- SMT.declare p (smtName a)    SMT.tInt
                    _  <- SMT.declare p (smtFinName a) SMT.tBool
                    SMT.assert p (SMT.geq e (SMT.int 0))




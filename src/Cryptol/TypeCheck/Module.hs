{-# Language BlockArguments #-}
{-# Language Trustworthy #-}
module Cryptol.TypeCheck.Module (doFunctorInst) where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad(unless,forM_)


import Cryptol.Utils.Panic(xxxTODO)
import Cryptol.Utils.Ident(Ident,Namespace(..))
import Cryptol.Parser.Position (Range,Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Name(nameIdent)
import Cryptol.ModuleSystem.Interface
          ( IfaceG(..), IfaceModParam(..), IfaceDecls(..), IfaceNames(..)
          , IfaceParams(..), IfaceDecl(..)
          , filterIfaceDecls
          )
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Error
import Cryptol.TypeCheck.Subst(Subst,abstractSubst,listParamSubst,apSubst)
import Cryptol.TypeCheck.Solve(proveImplication)
import Cryptol.TypeCheck.Monad
import Cryptol.TypeCheck.Instantiate(instantiateWith)

doFunctorInst ::
  Located Name                {- ^ Name for the new module -} ->
  Located (P.ImpName Name)    {- ^ Functor being instantiation -} ->
  P.ModuleInstanceArgs Name   {- ^ Instance arguments -} ->
  Map Name Name               {- ^ Basic instantiation -} ->
  InferM ()
doFunctorInst m f as inst =
  do mf    <- lookupFunctor (thing f)
     argIs <- checkArity (srcRange f) mf as
     (tySus,valRens) <- unzip <$> mapM checkArg argIs

     pure ()


-- | Validate a functor application, just checking the argument names
checkArity ::
  Range             {- ^ Location for reporting errors -} ->
  ModuleG ()        {- ^ The functor being instantiated -} ->
  P.ModuleInstanceArgs Name {- ^ The arguments -} ->
  InferM [ (Range, IfaceModParam, IfaceG ()) ]
  {- ^ Associates functor parameters with the interfaces of the
       instantiating modules -}
checkArity r mf args =
  case args of

    P.DefaultInstArg arg ->
      let i = Located { srcRange = srcRange arg
                      , thing    = head (Map.keys ps0)
                      }
      in checkArgs [] ps0 [ P.ModuleInstanceArg i arg ]

    P.NamedInstArgs as -> checkArgs [] ps0 as

  where
  ps0 = mParams mf

  checkArgs done ps as =
    case as of

      [] -> do forM_ (Map.keys ps) \p ->
                 recordErrorLoc (Just r) (FunctorInstanceMissingArgument p)
               pure done

      P.ModuleInstanceArg ll lm : more ->
        case Map.lookup (thing ll) ps of
          Just i ->
            do mo <- lookupModule (thing lm)
               checkArgs ((srcRange lm, i, mo) : done)
                         (Map.delete (thing ll) ps) more
          Nothing ->
            do recordErrorLoc (Just (srcRange ll))
                              (FunctorInstanceBadArgument (thing ll))
               checkArgs done ps more


checkArg :: (Range, IfaceModParam, IfaceG ()) -> InferM (Subst, Map Name Expr)
checkArg (r,expect,actual) =
  do tRens <- mapM (checkParamType r tyMap) (Map.toList (ifParamTypes params))
     let renSu = abstractSubst (concat tRens)

     addGoals [ Goal
                  { goalSource = CtModuleInstance
                  , goalRange  = r -- location in signature: srcRange lc
                  , goal       = apSubst renSu (thing lc)
                  } | lc <- ifParamConstraints params ]

     -- Available value names
     let fromD d = (ifDeclName d, ifDeclSig d)
         vMap = nameMapToIdentMap fromD (ifDecls decls)

     vRen <- Map.fromList . concat <$>
                mapM (checkParamValue r vMap)
                     [ (i, s { mvpType = apSubst renSu (mvpType s) })
                     | (i,s) <- Map.toList (ifParamFuns params) ]

     pure (renSu, vRen)




  where
  params = ifmpParameters expect

  localNames = ifsDefines (ifNames actual)
  isLocal x  = x `Set.member` localNames
  decls      = filterIfaceDecls isLocal (ifPublic actual)

  -- Available type names
  tyMap      = Map.unions [ nameMapToIdentMap fromTS      (ifTySyns decls)
                          , nameMapToIdentMap fromNewtype (ifNewtypes decls)
                          , nameMapToIdentMap fromPrimT   (ifAbstractTypes decls)
                          ]

  fromTS ts      = (kindOf ts, tsDef ts)
  fromNewtype nt = (kindOf nt, TNewtype nt [])
  fromPrimT pt   = (kindOf pt, TCon (abstractTypeTC pt) [])


nameMapToIdentMap :: (a -> b) -> Map Name a -> Map Ident b
nameMapToIdentMap f m =
  Map.fromList [ (nameIdent n, f v) | (n,v) <- Map.toList m ]




-- | Check a type parameter to a module.
checkParamType ::
  Range                 {- ^ Location for error reporting -} ->
  Map Ident (Kind,Type) {- ^ Actual types -} ->
  (Name,ModTParam)      {- ^ Type parameter -} ->
  InferM [(Name,Type)]  {- ^ Mapping from parameter name to actual type -}
checkParamType r tyMap (name,mp) =
  let i       = nameIdent name
      expectK = mtpKind mp
  in
  case Map.lookup i tyMap of
    Nothing ->
      do recordErrorLoc (Just r) (FunctorInstanceMissingName NSType i)
         pure []
    Just (actualK,actualT) ->
      do unless (expectK == actualK)
           (recordErrorLoc (Just r)
                           (KindMismatch (Just (TVFromModParam name))
                                                  expectK actualK))
         pure [(name, actualT)]

-- | Check a value parameter to a module.
checkParamValue ::
  Range                   {- ^ Location for error reporting -} ->
  Map Ident (Name,Schema) {- ^ Actual values -} ->
  (Name, ModVParam)       {- ^ The parameter we are checking -} ->
  InferM [(Name,Expr)]    {- ^ Mapping from parameter name to actual names -}
checkParamValue r vMap (name,mp) =
  let i        = nameIdent name
      expectT  = mvpType mp
  in case Map.lookup i vMap of
       Nothing ->
         do recordErrorLoc (Just r) (FunctorInstanceMissingName NSValue i)
            pure []
       Just actual ->
         do e <- mkParamDef r (name,expectT) actual
            pure [(name,e)]
{-
         do unless (sameSchema expectT actualT) $
              (recordErrorLoc (Just r) (SchemaMismatch i expectT actualT))
            pure [(name,EVar actualName)]
-}


{- | Make an "adaptor" that instantiates the paramter into the form expected
by the functor.  If the actual type is:

> {x} P => t

and the provided type is:

> f : {y} Q => s

The result, if successful would be:

  /\x \{P}. f @a {Q}

To do this we need to find types `a` to instantiate `y`, and prove that:
  {x} P => Q[a/y] /\ s = t
-}

mkParamDef ::
  Range           {- ^ Location of instantiation for error reporting -} ->
  (Name,Schema)   {- ^ Name and type of parameter -} ->
  (Name,Schema)   {- ^ Name and type of actual argument -} ->
  InferM Expr
mkParamDef r (pname,wantedS) (arg,actualS) =
  do (e,todo) <- collectGoals
          $ withTParams (sVars wantedS)
            do (e,t) <- instantiateWith pname(EVar arg) actualS []
               props <- unify WithSource { twsType   = sType wantedS
                                         , twsSource = TVFromModParam arg
                                         , twsRange  = Just r
                                         }
                        t
               newGoals CtModuleInstance props
               pure e
     su <- proveImplication (Just pname)
                            (sVars wantedS)
                            (sProps wantedS)
                            todo
     let res  = foldr ETAbs     res1            (sVars wantedS)
         res1 = foldr EProofAbs (apSubst su e)  (sProps wantedS)

     pure res





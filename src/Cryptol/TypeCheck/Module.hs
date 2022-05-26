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
import Cryptol.TypeCheck.Subst(Subst,listParamSubst,apSubst)
import Cryptol.TypeCheck.Monad
import Cryptol.IR.TraverseNames(mapNames, TraverseNames)

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


checkArg :: (Range, IfaceModParam, IfaceG ()) -> InferM (Subst, Map Name Name)
checkArg (r,expect,actual) =
  do tRens <- mapM (checkParamType r tyMap) (Map.toList (ifParamTypes params))
     let renSu = listParamSubst (concat tRens)

     addGoals [ Goal
                  { goalSource = CtModuleInstance
                  , goalRange  = r -- location in signature: srcRange lc
                  , goal       = apSubst renSu (thing lc)
                  } | lc <- ifParamConstraints params ]

     -- Available value names
     let fromD d = (ifDeclName d, ifDeclSig d)
         vMap = nameMapToIdentMap fromD (ifDecls decls)

     vRen <- Map.fromList <$>
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




checkParamType ::
  Range                 {- ^ Location for error reporting -} ->
  Map Ident (Kind,Type) {- ^ Actual types -} ->
  (Name,ModTParam)      {- ^ Type parameter -} ->
  InferM [(TParam,Type)]  {- ^ Mapping from parameter name to actual type -}
checkParamType r tyMap (name,mp) =
  let i       = nameIdent name
      expectK = mtpKind mp
      pvar    = mtpParam mp
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
         pure [(pvar, actualT)]

checkParamValue ::
  Range                   {- ^ Location for error reporting -} ->
  Map Ident (Name,Schema) {- ^ Actual values -} ->
  (Name, ModVParam)       {- ^ The parameter we are checking -} ->
  InferM (Name,Name)      {- ^ Mapping from parameter name to actual names -}
checkParamValue r vMap (name,mp) =
  let i        = nameIdent name
      expectT  = mvpType mp
  in case Map.lookup i vMap of
       Nothing ->
         do recordErrorLoc (Just r) (FunctorInstanceMissingName NSValue i)
            pure (name,name)
       Just (actualName,actualT) ->
         do unless (sameSchema expectT actualT) $
              (recordErrorLoc (Just r) (SchemaMismatch i expectT actualT))
            pure (name,actualName)

{- | Compare two schemas for equality.  We are quite strict here because
module instantiation is done by name (e.g., think linking).  As a result,
the types need to match precisely, otherwise the call sites won't work.

Some future ideas for quality of life improvements:
  * compute an "adaptor" module that is derived from an exisiting instantitiation
    module and automatically adjust the time.
  * change the translation so that instantitation does not simply change names
    but allows replacing them with expressions, which would require careful
    rewrites at the call sites; this amounts to "inlining" the adaptor module
    from the first bullet.
-}
sameSchema :: Schema -> Schema -> Bool
sameSchema t1 t2 = map kindOf as == map kindOf bs
                && apSubst su (sProps t1, sType t1) == (sProps t2, sType t2)
  where
  as = sVars t1
  bs = sVars t2
  su = listParamSubst [ (a, TVar (TVBound b)) | (a,b) <- zip as bs ]



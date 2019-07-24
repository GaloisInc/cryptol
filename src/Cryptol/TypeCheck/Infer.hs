-- |
-- Module      :  Cryptol.TypeCheck.Infer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Assumes that the `NoPat` pass has been run.

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Infer
  ( checkE
  , checkSigB
  , inferModule
  , inferBinds
  , inferDs
  )
where

import           Cryptol.ModuleSystem.Name (asPrim,lookupPrimDecl,nameLoc)
import           Cryptol.Parser.Position
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.ModuleSystem.Exports as P
import           Cryptol.TypeCheck.AST hiding (tSub,tMul,tExp)
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Error
import           Cryptol.TypeCheck.Solve
import           Cryptol.TypeCheck.SimpType(tMul)
import           Cryptol.TypeCheck.Kind(checkType,checkSchema,checkTySyn,
                                        checkPropSyn,checkNewtype,
                                        checkParameterType,
                                        checkPrimType,
                                        checkParameterConstraints)
import           Cryptol.TypeCheck.Instantiate
import           Cryptol.TypeCheck.Depends
import           Cryptol.TypeCheck.Subst (listSubst,apSubst,(@@),isEmptySubst)
import           Cryptol.TypeCheck.Solver.InfNat(genLog)
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.PP

import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.List(foldl',sortBy)
import           Data.Either(partitionEithers)
import           Data.Maybe(mapMaybe,isJust, fromMaybe)
import           Data.List(partition,find)
import           Data.Graph(SCC(..))
import           Data.Traversable(forM)
import           Control.Monad(zipWithM,unless,foldM)



inferModule :: P.Module Name -> InferM Module
inferModule m =
  inferDs (P.mDecls m) $ \ds1 ->
    do proveModuleTopLevel
       ts <- getTSyns
       nts <- getNewtypes
       ats <- getAbstractTypes
       pTs <- getParamTypes
       pCs <- getParamConstraints
       pFuns <- getParamFuns
       return Module { mName      = thing (P.mName m)
                     , mExports   = P.modExports m
                     , mImports   = map thing (P.mImports m)
                     , mTySyns    = Map.mapMaybe onlyLocal ts
                     , mNewtypes  = Map.mapMaybe onlyLocal nts
                     , mPrimTypes = Map.mapMaybe onlyLocal ats
                     , mParamTypes = pTs
                     , mParamConstraints = pCs
                     , mParamFuns = pFuns
                     , mDecls     = ds1
                     }
  where
  onlyLocal (IsLocal, x)    = Just x
  onlyLocal (IsExternal, _) = Nothing



-- | Construct a primitive in the parsed AST.
mkPrim :: String -> InferM (P.Expr Name)
mkPrim str =
  do nm <- mkPrim' str
     return (P.EVar nm)

-- | Construct a primitive in the parsed AST.
mkPrim' :: String -> InferM Name
mkPrim' str =
  do prims <- getPrimMap
     return (lookupPrimDecl (packIdent str) prims)



desugarLiteral :: Bool -> P.Literal -> InferM (P.Expr Name)
desugarLiteral fixDec lit =
  do l <- curRange
     numberPrim <- mkPrim "number"
     let named (x,y)  = P.NamedInst
                        P.Named { name = Located l (packIdent x), value = y }
         number fs    = P.EAppT numberPrim (map named fs)
         tBits n = P.TSeq (P.TNum n) P.TBit

     return $ case lit of

       P.ECNum num info ->
         number $ [ ("val", P.TNum num) ] ++ case info of
           P.BinLit n    -> [ ("rep", tBits (1 * toInteger n)) ]
           P.OctLit n    -> [ ("rep", tBits (3 * toInteger n)) ]
           P.HexLit n    -> [ ("rep", tBits (4 * toInteger n)) ]
           P.CharLit     -> [ ("rep", tBits (8 :: Integer)) ]
           P.DecLit
            | fixDec     -> if num == 0
                              then [ ("rep", tBits 0)]
                              else case genLog num 2 of
                                     Just (x,_) -> [ ("rep", tBits (x + 1)) ]
                                     _          -> []
            | otherwise  -> [ ]
           P.PolyLit _n  -> [ ("rep", P.TSeq P.TWild P.TBit) ]

       P.ECString s ->
          P.ETyped (P.EList [ P.ELit (P.ECNum (toInteger (fromEnum c))
                            P.CharLit) | c <- s ])
                   (P.TSeq P.TWild (P.TSeq (P.TNum 8) P.TBit))



-- | Infer the type of an expression with an explicit instantiation.
appTys :: P.Expr Name -> [TypeArg] -> Type -> InferM Expr
appTys expr ts tGoal =
  case expr of
    P.EVar x ->
      do res <- lookupVar x
         (e',t) <- case res of
           ExtVar s   -> instantiateWith x (EVar x) s ts
           CurSCC e t -> do checkNoParams ts
                            return (e,t)

         checkHasType t tGoal
         return e'

    P.ELit l -> do e <- desugarLiteral False l
                   appTys e ts tGoal


    P.EAppT e fs -> appTys e (map uncheckedTypeArg fs ++ ts) tGoal

    -- Here is an example of why this might be useful:
    -- f ` { x = T } where type T = ...
    P.EWhere e ds ->
      inferDs ds $ \ds1 -> do e1 <- appTys e ts tGoal
                              return (EWhere e1 ds1)
         -- XXX: Is there a scoping issue here?  I think not, but check.

    P.ELocated e r ->
      inRange r (appTys e ts tGoal)

    P.ENeg        {} -> mono
    P.EComplement {} -> mono
    P.EGenerate   {} -> mono

    P.ETuple    {} -> mono
    P.ERecord   {} -> mono
    P.EUpd      {} -> mono
    P.ESel      {} -> mono
    P.EList     {} -> mono
    P.EFromTo   {} -> mono
    P.EInfFrom  {} -> mono
    P.EComp     {} -> mono
    P.EApp      {} -> mono
    P.EIf       {} -> mono
    P.ETyped    {} -> mono
    P.ETypeVal  {} -> mono
    P.EFun      {} -> mono
    P.ESplit    {} -> mono

    P.EParens e       -> appTys e ts tGoal
    P.EInfix a op _ b -> appTys (P.EVar (thing op) `P.EApp` a `P.EApp` b) ts tGoal

  where mono = do e' <- checkE expr tGoal
                  checkNoParams ts
                  return e'

checkNoParams :: [TypeArg] -> InferM ()
checkNoParams ts =
  case pos of
    p : _ -> do r <- case tyArgType p of
                       Unchecked t | Just r <- getLoc t -> pure r
                       _ -> curRange
                inRange r (recordError TooManyPositionalTypeParams)
    _ -> mapM_ badNamed named
  where
  badNamed l =
    case tyArgName l of
      Just i  -> recordError (UndefinedTypeParameter i)
      Nothing -> return ()

  (named,pos) = partition (isJust . tyArgName) ts


checkTypeOfKind :: P.Type Name -> Kind -> InferM Type
checkTypeOfKind ty k = checkType ty (Just k)


-- | Infer the type of an expression, and translate it to a fully elaborated
-- core term.
checkE :: P.Expr Name -> Type -> InferM Expr
checkE expr tGoal =
  case expr of
    P.EVar x ->
      do res <- lookupVar x
         (e',t) <- case res of
                     ExtVar s   -> instantiateWith x (EVar x) s []
                     CurSCC e t -> return (e, t)

         checkHasType t tGoal
         return e'

    P.ENeg e ->
      do prim <- mkPrim "negate"
         checkE (P.EApp prim e) tGoal

    P.EComplement e ->
      do prim <- mkPrim "complement"
         checkE (P.EApp prim e) tGoal

    P.EGenerate e ->
      do prim <- mkPrim "generate"
         checkE (P.EApp prim e) tGoal

    P.ELit l@(P.ECNum _ P.DecLit) ->
      do e <- desugarLiteral False l
         -- NOTE: When 'l' is a decimal literal, 'desugarLiteral' does
         -- not generate an instantiation for the 'rep' type argument
         -- of the 'number' primitive. Therefore we explicitly
         -- instantiate 'rep' to 'tGoal' in this case to avoid
         -- generating an unnecessary unification variable.
         loc <- curRange
         let arg = TypeArg { tyArgName = Just (Located loc (packIdent "rep"))
                           , tyArgType = Checked tGoal
                           }
         appTys e [arg] tGoal

    P.ELit l -> (`checkE` tGoal) =<< desugarLiteral False l

    P.ETuple es ->
      do etys <- expectTuple (length es) tGoal
         es'  <- zipWithM checkE es etys
         return (ETuple es')

    P.ERecord fs ->
      do (ns,es,ts) <- unzip3 `fmap` expectRec fs tGoal
         es' <- zipWithM checkE es ts
         return (ERec (zip ns es'))

    P.EUpd x fs -> checkRecUpd x fs tGoal

    P.ESel e l ->
      do t <- newType (selSrc l) KType
         e' <- checkE e t
         f <- newHasGoal l t tGoal
         return (hasDoSelect f e')

    P.EList [] ->
      do (len,a) <- expectSeq tGoal
         expectFin 0 len
         return (EList [] a)

    P.EList es ->
      do (len,a) <- expectSeq tGoal
         expectFin (length es) len
         es' <- mapM (`checkE` a) es
         return (EList es' a)

    P.EFromTo t1 mbt2 t3 mety ->
      do l <- curRange
         let fs0 =
               case mety of
                 Just ety -> [("a", ety)]
                 Nothing -> []
         let (c,fs) =
               case mbt2 of
                 Nothing ->
                    ("fromTo", ("last", t3) : fs0)
                 Just t2 ->
                    ("fromThenTo", ("next",t2) : ("last",t3) : fs0)

         prim <- mkPrim c
         let e' = P.EAppT prim
                  [ P.NamedInst P.Named { name = Located l (packIdent x), value = y }
                  | (x,y) <- ("first",t1) : fs
                  ]

         checkE e' tGoal

    P.EInfFrom e1 Nothing ->
      do prim <- mkPrim "infFrom"
         checkE (P.EApp prim e1) tGoal

    P.EInfFrom e1 (Just e2) ->
      do prim <- mkPrim "infFromThen"
         checkE (P.EApp (P.EApp prim e1) e2) tGoal

    P.EComp e mss ->
      do (mss', dss, ts) <- unzip3 `fmap` zipWithM inferCArm [ 1 .. ] mss
         (len,a) <- expectSeq tGoal

         newGoals CtComprehension =<< unify len =<< smallest ts

         ds     <- combineMaps dss
         e'     <- withMonoTypes ds (checkE e a)
         return (EComp len a e' mss')

    P.EAppT e fs -> appTys e (map uncheckedTypeArg fs) tGoal

    P.EApp fun@(dropLoc -> P.EApp (dropLoc -> P.EVar c) _)
           arg@(dropLoc -> P.ELit l)
      | Just n <- asPrim c
      , n `elem` map packIdent [ "<<", ">>", "<<<", ">>>" , "@", "!" ] ->
        do newArg <- do l1 <- desugarLiteral True l
                        return $ case arg of
                                   P.ELocated _ pos -> P.ELocated l1 pos
                                   _ -> l1
           checkE (P.EApp fun newArg) tGoal

    P.EApp e1 e2 ->
      do t1  <- newType (TypeOfArg Nothing) KType
         e1' <- checkE e1 (tFun t1 tGoal)
         e2' <- checkE e2 t1
         return (EApp e1' e2')

    P.EIf e1 e2 e3 ->
      do e1'      <- checkE e1 tBit
         e2'      <- checkE e2 tGoal
         e3'      <- checkE e3 tGoal
         return (EIf e1' e2' e3')

    P.EWhere e ds ->
      inferDs ds $ \ds1 -> do e1 <- checkE e tGoal
                              return (EWhere e1 ds1)

    P.ETyped e t ->
      do tSig <- checkTypeOfKind t KType
         e'   <- checkE e tSig
         checkHasType tSig tGoal
         return e'

    P.ETypeVal t ->
      do l <- curRange
         prim <- mkPrim "number"
         checkE (P.EAppT prim
                  [P.NamedInst
                   P.Named { name = Located l (packIdent "val")
                           , value = t }]) tGoal

    P.EFun ps e -> checkFun (text "anonymous function") ps e tGoal

    P.ELocated e r  -> inRange r (checkE e tGoal)

    P.ESplit e ->
      do prim <- mkPrim "splitAt"
         checkE (P.EApp prim e) tGoal

    P.EInfix a op _ b -> checkE (P.EVar (thing op) `P.EApp` a `P.EApp` b) tGoal

    P.EParens e -> checkE e tGoal


selSrc :: P.Selector -> TVarSource
selSrc l = case l of
             RecordSel la _ -> TypeOfRecordField la
             TupleSel n _   -> TypeOfTupleField n
             ListSel _ _    -> TypeOfSeqElement

checkRecUpd :: Maybe (P.Expr Name) -> [ P.UpdField Name ] -> Type -> InferM Expr
checkRecUpd mb fs tGoal =
  case mb of

    -- { _ | fs } ~~>  \r -> { r | fs }
    Nothing ->
      do r <- newParamName (packIdent "r")
         let p  = P.PVar Located { srcRange = nameLoc r, thing = r }
             fe = P.EFun [p] (P.EUpd (Just (P.EVar r)) fs)
         checkE fe tGoal

    Just e ->
      do e1 <- checkE e tGoal
         foldM doUpd e1 fs

  where
  doUpd e (P.UpdField how sels v) =
    case sels of
      [l] ->
        case how of
          P.UpdSet ->
            do ft <- newType (selSrc s) KType
               v1 <- checkE v ft
               d  <- newHasGoal s tGoal ft
               pure (hasDoSet d e v1)
          P.UpdFun ->
             do ft <- newType (selSrc s) KType
                v1 <- checkE v (tFun ft ft)
                d  <- newHasGoal s tGoal ft
                tmp <- newParamName (packIdent "rf")
                let e' = EVar tmp
                pure $ hasDoSet d e' (EApp v1 (hasDoSelect d e'))
                       `EWhere`
                       [  NonRecursive
                          Decl { dName        = tmp
                               , dSignature   = tMono tGoal
                               , dDefinition  = DExpr e
                               , dPragmas     = []
                               , dInfix       = False
                               , dFixity      = Nothing
                               , dDoc         = Nothing
                               } ]

        where s = thing l
      _ -> panic "checkRecUpd/doUpd" [ "Expected exactly 1 field label"
                                     , "Got: " ++ show (length sels)
                                     ]


expectSeq :: Type -> InferM (Type,Type)
expectSeq ty =
  case ty of

    TUser _ _ ty' ->
         expectSeq ty'

    TCon (TC TCSeq) [a,b] ->
         return (a,b)

    TVar _ ->
      do tys@(a,b) <- genTys
         newGoals CtExactType =<< unify ty (tSeq a b)
         return tys

    _ ->
      do tys@(a,b) <- genTys
         recordError (TypeMismatch ty (tSeq a b))
         return tys
  where
  genTys =
    do a <- newType LenOfSeq KNum
       b <- newType TypeOfSeqElement KType
       return (a,b)


expectTuple :: Int -> Type -> InferM [Type]
expectTuple n ty =
  case ty of

    TUser _ _ ty' ->
         expectTuple n ty'

    TCon (TC (TCTuple n')) tys | n == n' ->
         return tys

    TVar _ ->
      do tys <- genTys
         newGoals CtExactType =<< unify ty (tTuple tys)
         return tys

    _ ->
      do tys <- genTys
         recordError (TypeMismatch ty (tTuple tys))
         return tys

  where
  genTys =forM [ 0 .. n - 1 ] $ \ i -> newType (TypeOfTupleField i) KType

expectRec :: [P.Named a] -> Type -> InferM [(Ident,a,Type)]
expectRec fs ty =
  case ty of

    TUser _ _ ty' ->
         expectRec fs ty'

    TRec ls | Just tys <- mapM checkField ls ->
         return tys

    _ ->
      do (tys,res) <- genTys
         case ty of
           TVar TVFree{} -> do ps <- unify ty (TRec tys)
                               newGoals CtExactType ps
           _ -> recordError (TypeMismatch ty (TRec tys))
         return res

  where
  checkField (n,t) =
    do f <- find (\f -> thing (P.name f) == n) fs
       return (thing (P.name f), P.value f, t)

  genTys =
    do res <- forM fs $ \ f ->
             do let field = thing (P.name f)
                t <- newType (TypeOfRecordField field) KType
                return (field, P.value f, t)

       let (ls,_,ts) = unzip3 res
       return (zip ls ts, res)


expectFin :: Int -> Type -> InferM ()
expectFin n ty =
  case ty of

    TUser _ _ ty' ->
         expectFin n ty'

    TCon (TC (TCNum n')) [] | toInteger n == n' ->
         return ()

    _ ->
      do newGoals CtExactType =<< unify ty (tNum n)

expectFun :: Int -> Type -> InferM ([Type],Type)
expectFun  = go []
  where

  go tys arity ty
    | arity > 0 =
      case ty of

        TUser _ _ ty' ->
             go tys arity ty'

        TCon (TC TCFun) [a,b] ->
             go (a:tys) (arity - 1) b

        _ ->
          do args <- genArgs arity
             res  <- newType TypeOfRes KType
             case ty of
               TVar TVFree{} -> do ps <- unify ty (foldr tFun res args)
                                   newGoals CtExactType  ps
               _             -> recordError (TypeMismatch ty (foldr tFun res args))
             return (reverse tys ++ args, res)

    | otherwise =
      return (reverse tys, ty)

  genArgs arity = forM [ 1 .. arity ] $
                    \ ix -> newType (TypeOfArg (Just ix)) KType


checkHasType :: Type -> Type -> InferM ()
checkHasType inferredType givenType =
  do ps <- unify givenType inferredType
     case ps of
       [] -> return ()
       _  -> newGoals CtExactType ps


checkFun :: Doc -> [P.Pattern Name] -> P.Expr Name -> Type -> InferM Expr
checkFun _    [] e tGoal = checkE e tGoal
checkFun desc ps e tGoal =
  inNewScope $
  do let descs = [ text "type of" <+> ordinal n <+> text "argument"
                     <+> text "of" <+> desc | n <- [ 1 :: Int .. ] ]

     (tys,tRes) <- expectFun (length ps) tGoal
     largs      <- sequence (zipWith3 checkP descs ps tys)
     let ds = Map.fromList [ (thing x, x { thing = t }) | (x,t) <- zip largs tys ]
     e1         <- withMonoTypes ds (checkE e tRes)

     let args = [ (thing x, t) | (x,t) <- zip largs tys ]
     return (foldr (\(x,t) b -> EAbs x t b) e1 args)


{-| The type the is the smallest of all -}
smallest :: [Type] -> InferM Type
smallest []   = newType LenOfSeq KNum
smallest [t]  = return t
smallest ts   = do a <- newType LenOfSeq KNum
                   newGoals CtComprehension [ a =#= foldr1 tMin ts ]
                   return a

checkP :: Doc -> P.Pattern Name -> Type -> InferM (Located Name)
checkP desc p tGoal =
  do (x, t) <- inferP desc p
     ps <- unify tGoal (thing t)
     let rng   = fromMaybe emptyRange $ getLoc p
     let mkErr = recordError . UnsolvedGoals False . (:[])
                                                   . Goal (CtPattern desc) rng
     mapM_ mkErr ps
     return (Located (srcRange t) x)

{-| Infer the type of a pattern.  Assumes that the pattern will be just
a variable. -}
inferP :: Doc -> P.Pattern Name -> InferM (Name, Located Type)
inferP desc pat =
  case pat of

    P.PVar x0 ->
      do a   <- inRange (srcRange x0) (newType (DefinitionOf (thing x0)) KType)
         return (thing x0, x0 { thing = a })

    P.PTyped p t ->
      do tSig <- checkTypeOfKind t KType
         ln   <- checkP desc p tSig
         return (thing ln, ln { thing = tSig })

    _ -> tcPanic "inferP" [ "Unexpected pattern:", show pat ]



-- | Infer the type of one match in a list comprehension.
inferMatch :: P.Match Name -> InferM (Match, Name, Located Type, Type)
inferMatch (P.Match p e) =
  do (x,t) <- inferP (text "a value bound by a generator in a comprehension") p
     n     <- newType LenOfCompGen KNum
     e'    <- checkE e (tSeq n (thing t))
     return (From x n (thing t) e', x, t, n)

inferMatch (P.MatchLet b)
  | P.bMono b =
  do let rng = srcRange (P.bName b)
     a <- inRange rng (newType (DefinitionOf (thing (P.bName b))) KType)
     b1 <- checkMonoB b a
     return (Let b1, dName b1, Located (srcRange (P.bName b)) a, tNum (1::Int))

  | otherwise = tcPanic "inferMatch"
                      [ "Unexpected polymorphic match let:", show b ]

-- | Infer the type of one arm of a list comprehension.
inferCArm :: Int -> [P.Match Name] -> InferM
              ( [Match]
              , Map Name (Located Type)-- defined vars
              , Type                   -- length of sequence
              )

inferCArm _ [] = panic "inferCArm" [ "Empty comprehension arm" ]
inferCArm _ [m] =
  do (m1, x, t, n) <- inferMatch m
     return ([m1], Map.singleton x t, n)

inferCArm armNum (m : ms) =
  do (m1, x, t, n)  <- inferMatch m
     (ms', ds, n')  <- withMonoType (x,t) (inferCArm armNum ms)
     newGoals CtComprehension [ pFin n' ]
     return (m1 : ms', Map.insertWith (\_ old -> old) x t ds, tMul n n')

-- | @inferBinds isTopLevel isRec binds@ performs inference for a
-- strongly-connected component of 'P.Bind's.
-- If any of the members of the recursive group are already marked
-- as monomorphic, then we don't do generalzation.
-- If @isTopLevel@ is true,
-- any bindings without type signatures will be generalized. If it is
-- false, and the mono-binds flag is enabled, no bindings without type
-- signatures will be generalized, but bindings with signatures will
-- be unaffected.
inferBinds :: Bool -> Bool -> [P.Bind Name] -> InferM [Decl]
inferBinds isTopLevel isRec binds =
  do -- when mono-binds is enabled, and we're not checking top-level
     -- declarations, mark all bindings lacking signatures as monomorphic
     monoBinds <- getMonoBinds
     let (sigs,noSigs) = partition (isJust . P.bSignature) binds
         monos         = sigs ++ [ b { P.bMono = True } | b <- noSigs ]
         binds' | any P.bMono binds           = monos
                | monoBinds && not isTopLevel = monos
                | otherwise                   = binds

         check exprMap =
        {- Guess type is here, because while we check user supplied signatures
           we may generate additional constraints. For example, `x - y` would
           generate an additional constraint `x >= y`. -}
           do (newEnv,todos) <- unzip `fmap` mapM (guessType exprMap) binds'
              let otherEnv = filter isExt newEnv

              let (sigsAndMonos,noSigGen) = partitionEithers todos

              let prepGen = collectGoals
                          $ do bs <- sequence noSigGen
                               simplifyAllConstraints
                               return bs

              if isRec
                then
                  -- First we check the bindings with no signatures
                  -- that need to be generalized.
                  do (bs1,cs) <- withVarTypes newEnv prepGen

                     -- We add these to the environment, so their fvs are
                     -- not generalized.
                     genCs <- withVarTypes otherEnv (generalize bs1 cs)

                     -- Then we do all the rest,
                     -- using the newly inferred poly types.
                     let newEnv' = map toExt bs1 ++ otherEnv
                     done <- withVarTypes newEnv' (sequence sigsAndMonos)
                     return (done,genCs)

                else
                  do done      <- sequence sigsAndMonos
                     (bs1, cs) <- prepGen
                     genCs     <- generalize bs1 cs
                     return (done,genCs)

     rec
       let exprMap = Map.fromList (map monoUse genBs)
       (doneBs, genBs) <- check exprMap

     simplifyAllConstraints

     return (doneBs ++ genBs)

  where
  toExt d = (dName d, ExtVar (dSignature d))
  isExt (_,y) = case y of
                  ExtVar _ -> True
                  _        -> False

  monoUse d = (x, withQs)
    where
    x  = dName d
    as = sVars (dSignature d)
    qs = sProps (dSignature d)

    appT e a = ETApp e (TVar (tpVar a))
    appP e _ = EProofApp e

    withTys  = foldl' appT (EVar x) as
    withQs   = foldl' appP withTys  qs





{- | Come up with a type for recursive calls to a function, and decide
     how we are going to be checking the binding.
     Returns: (Name, type or schema, computation to check binding)

     The `exprMap` is a thunk where we can lookup the final expressions
     and we should be careful not to force it.
-}
guessType :: Map Name Expr -> P.Bind Name ->
              InferM ( (Name, VarType)
                     , Either (InferM Decl)    -- no generalization
                              (InferM Decl)    -- generalize these
                     )
guessType exprMap b@(P.Bind { .. }) =
  case bSignature of

    Just s ->
      do s1 <- checkSchema AllowWildCards s
         return ((name, ExtVar (fst s1)), Left (checkSigB b s1))

    Nothing
      | bMono ->
         do t <- newType (DefinitionOf name) KType
            let schema = Forall [] [] t
            return ((name, ExtVar schema), Left (checkMonoB b t))

      | otherwise ->

        do t <- newType (DefinitionOf name) KType
           let noWay = tcPanic "guessType" [ "Missing expression for:" ,
                                                                show name ]
               expr  = Map.findWithDefault noWay name exprMap

           return ((name, CurSCC expr t), Right (checkMonoB b t))
  where
  name = thing bName



{- | The inputs should be declarations with monomorphic types
(i.e., of the form `Forall [] [] t`). -}
generalize :: [Decl] -> [Goal] -> InferM [Decl]

{- This may happen because we have monomorphic bindings.
In this case we may get some goal, due to the monomorphic bindings,
but the group of components is empty. -}
generalize [] gs0 =
  do addGoals gs0
     return []


generalize bs0 gs0 =
  do {- First, we apply the accumulating substitution to the goals
        and the inferred types, to ensure that we have the most up
        to date information. -}
     gs <- applySubstGoals gs0
     bs <- forM bs0 $ \b -> do s <- applySubst (dSignature b)
                               return b { dSignature = s }

     -- Next, we figure out which of the free variables need to be generalized
     -- Variables apearing in the types of monomorphic bindings should
     -- not be generalizedr.
     let goalFVS g  = Set.filter isFreeTV $ fvs $ goal g
         inGoals    = Set.unions $ map goalFVS gs
         inSigs     = Set.filter isFreeTV $ fvs $ map dSignature bs
         candidates = (Set.union inGoals inSigs)

     asmpVs <- varsWithAsmps

     let gen0          = Set.difference candidates asmpVs
         stays g       = any (`Set.member` gen0) $ Set.toList $ goalFVS g
         (here0,later) = partition stays gs
     addGoals later   -- these ones we keep around for to solve later

     let maybeAmbig = Set.toList (Set.difference gen0 inSigs)

     {- See if we might be able to default some of the potentially ambiguous
        variables using the constraints that will be part of the newly
        generalized schema.  -}
     let (as0,here1,defSu,ws) = defaultAndSimplify maybeAmbig here0

     extendSubst defSu
     mapM_ recordWarning ws
     let here = map goal here1


     {- This is the variables we'll be generalizing:
          * any ones that survived the defaulting
          * and vars in the inferred types that do not appear anywhere else. -}
     let as   = sortBy numFst
              $ as0 ++ Set.toList (Set.difference inSigs asmpVs)
         asPs = [ TParam { tpUnique = x, tpKind = k, tpFlav = TPOther Nothing
                         , tpInfo = i  } | TVFree x k _ i <- as ]

     {- Finally, we replace free variables with bound ones, and fix-up
        the definitions as needed to reflect that we are now working
        with polymorphic things. For example, apply each occurrence to the
        type parameters. -}
     totSu <- getSubst
     let
         su     = listSubst (zip as (map (TVar . tpVar) asPs)) @@ totSu
         qs     = concatMap (pSplitAnd . apSubst su) here

         genE e = foldr ETAbs (foldr EProofAbs (apSubst su e) qs) asPs
         genB d = d { dDefinition = case dDefinition d of
                                      DExpr e -> DExpr (genE e)
                                      DPrim   -> DPrim
                    , dSignature  = Forall asPs qs
                                  $ apSubst su $ sType $ dSignature d
                    }

     return (map genB bs)

  where
  numFst x y = case (kindOf x, kindOf y) of
                 (KNum, KNum) -> EQ
                 (KNum, _)    -> LT
                 (_,KNum)     -> GT
                 _            -> EQ

-- | Check a monomorphic binding.
checkMonoB :: P.Bind Name -> Type -> InferM Decl
checkMonoB b t =
  inRangeMb (getLoc b) $
  case thing (P.bDef b) of

    P.DPrim -> panic "checkMonoB" ["Primitive with no signature?"]

    P.DExpr e ->
      do e1 <- checkFun (pp (thing (P.bName b))) (P.bParams b) e t
         let f = thing (P.bName b)
         return Decl { dName = f
                     , dSignature = Forall [] [] t
                     , dDefinition = DExpr e1
                     , dPragmas = P.bPragmas b
                     , dInfix = P.bInfix b
                     , dFixity = P.bFixity b
                     , dDoc = P.bDoc b
                     }

-- XXX: Do we really need to do the defaulting business in two different places?
checkSigB :: P.Bind Name -> (Schema,[Goal]) -> InferM Decl
checkSigB b (Forall as asmps0 t0, validSchema) = case thing (P.bDef b) of

 -- XXX what should we do with validSchema in this case?
 P.DPrim ->
   do return Decl { dName       = thing (P.bName b)
                  , dSignature  = Forall as asmps0 t0
                  , dDefinition = DPrim
                  , dPragmas    = P.bPragmas b
                  , dInfix      = P.bInfix b
                  , dFixity     = P.bFixity b
                  , dDoc        = P.bDoc b
                  }

 P.DExpr e0 ->
  inRangeMb (getLoc b) $
  withTParams as $
  do (e1,cs0) <- collectGoals $
                do e1 <- checkFun (pp (thing (P.bName b))) (P.bParams b) e0 t0
                   addGoals validSchema
                   () <- simplifyAllConstraints  -- XXX: using `asmps` also?
                   return e1
     cs <- applySubstGoals cs0

     let findKeep vs keep todo =
          let stays (_,cvs)    = not $ Set.null $ Set.intersection vs cvs
              (yes,perhaps)    = partition stays todo
              (stayPs,newVars) = unzip yes
          in case stayPs of
               [] -> (keep,map fst todo)
               _  -> findKeep (Set.unions (vs:newVars)) (stayPs ++ keep) perhaps

     let (stay,leave) = findKeep (Set.fromList (map tpVar as)) []
                            [ (c, fvs c) | c <- cs ]

     addGoals leave

     asmps1 <- applySubstPreds asmps0

     su <- proveImplication (Just (thing (P.bName b))) as asmps1 stay
     extendSubst su

     let asmps  = concatMap pSplitAnd (apSubst su asmps1)
     t      <- applySubst t0
     e2     <- applySubst e1

     return Decl
        { dName       = thing (P.bName b)
        , dSignature  = Forall as asmps t
        , dDefinition = DExpr (foldr ETAbs (foldr EProofAbs e2 asmps) as)
        , dPragmas    = P.bPragmas b
        , dInfix      = P.bInfix b
        , dFixity     = P.bFixity b
        , dDoc        = P.bDoc b
        }

inferDs :: FromDecl d => [d] -> ([DeclGroup] -> InferM a) -> InferM a
inferDs ds continue = checkTyDecls =<< orderTyDecls (mapMaybe toTyDecl ds)
  where
  isTopLevel = isTopDecl (head ds)

  checkTyDecls (AT t mbD : ts) =
    do t1 <- checkParameterType t mbD
       withParamType t1 (checkTyDecls ts)

  checkTyDecls (TS t mbD : ts) =
    do t1 <- checkTySyn t mbD
       withTySyn t1 (checkTyDecls ts)

  checkTyDecls (PS t mbD : ts) =
    do t1 <- checkPropSyn t mbD
       withTySyn t1 (checkTyDecls ts)

  checkTyDecls (NT t mbD : ts) =
    do t1 <- checkNewtype t mbD
       withNewtype t1 (checkTyDecls ts)

  checkTyDecls (PT p mbD : ts) =
    do p1 <- checkPrimType p mbD
       withPrimType p1 (checkTyDecls ts)

  -- We checked all type synonyms, now continue with value-level definitions:
  checkTyDecls [] =
    do cs <- checkParameterConstraints (concatMap toParamConstraints ds)
       withParameterConstraints cs $
         do xs <- mapM checkParameterFun (mapMaybe toParamFun ds)
            withParamFuns xs $ checkBinds [] $ orderBinds $ mapMaybe toBind ds


  checkParameterFun x =
    do (s,gs) <- checkSchema NoWildCards (P.pfSchema x)
       su <- proveImplication (Just (thing (P.pfName x)))
                              (sVars s) (sProps s) gs
       unless (isEmptySubst su) $
         panic "checkParameterFun" ["Subst not empty??"]
       let n = thing (P.pfName x)
       return ModVParam { mvpName = n
                        , mvpType = s
                        , mvpDoc  = P.pfDoc x
                        , mvpFixity = P.pfFixity x
                        }

  checkBinds decls (CyclicSCC bs : more) =
     do bs1 <- inferBinds isTopLevel True bs
        foldr (\b m -> withVar (dName b) (dSignature b) m)
              (checkBinds (Recursive bs1 : decls) more)
              bs1

  checkBinds decls (AcyclicSCC c : more) =
    do ~[b] <- inferBinds isTopLevel False [c]
       withVar (dName b) (dSignature b) $
         checkBinds (NonRecursive b : decls) more

  -- We are done with all value-level definitions.
  -- Now continue with anything that's in scope of the declarations.
  checkBinds decls [] = continue (reverse decls)

tcPanic :: String -> [String] -> a
tcPanic l msg = panic ("[TypeCheck] " ++ l) msg

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Assumes that the `NoPat` pass has been run.

{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE RecursiveDo #-}
#else
{-# LANGUAGE DoRec, RecursiveDo #-}
#endif
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Infer where

import           Cryptol.Prims.Syntax(ECon(..))
import           Cryptol.Prims.Types(typeOf)
import           Cryptol.Parser.Position
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Names as P
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Solve
import           Cryptol.TypeCheck.Kind(checkType,checkSchema,checkTySyn,
                                          checkNewtype)
import           Cryptol.TypeCheck.Instantiate
import           Cryptol.TypeCheck.Depends
import           Cryptol.TypeCheck.Subst (listSubst,apSubst,fvs,(@@))
import           Cryptol.TypeCheck.Solver.InfNat(genLog)
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.PP

import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Either(partitionEithers)
import           Data.Maybe(mapMaybe,isJust)
import           Data.List(partition,find)
import           Data.Graph(SCC(..))
import           Data.Traversable(forM)
import           Control.Monad(when,zipWithM)

-- import Cryptol.Utils.Debug

inferModule :: P.Module -> InferM Module
inferModule m =
  inferDs (P.mDecls m) $ \ds1 ->
    do simplifyAllConstraints
       ts <- getTSyns
       nts <- getNewtypes
       return Module { mName    = thing (P.mName m)
                     , mExports = P.modExports m
                     , mImports = map thing (P.mImports m)
                     , mTySyns  = Map.mapMaybe onlyLocal ts
                     , mNewtypes = Map.mapMaybe onlyLocal nts
                     , mDecls   = ds1
                     }
  where
  onlyLocal (IsLocal, x)    = Just x
  onlyLocal (IsExternal, _) = Nothing

desugarLiteral :: Bool -> P.Literal -> InferM P.Expr
desugarLiteral fixDec lit =
  do l <- curRange
     let named (x,y)  = P.NamedInst
                        P.Named { name = Located l (Name x), value = P.TNum y }
         demote fs    = P.EAppT (P.ECon ECDemote) (map named fs)

     return $ case lit of

       P.ECNum num info ->
         demote $ [ ("val", num) ] ++ case info of
           P.BinLit n    -> [ ("bits", 1 * toInteger n) ]
           P.OctLit n    -> [ ("bits", 3 * toInteger n) ]
           P.HexLit n    -> [ ("bits", 4 * toInteger n) ]
           P.CharLit     -> [ ("bits", 8 :: Integer) ]
           P.DecLit
            | fixDec     -> if num == 0
                              then [ ("bits", 0)]
                              else case genLog num 2 of
                                     Just (x,_) -> [ ("bits", x + 1) ]
                                     _          -> []
            | otherwise  -> [ ]
           P.PolyLit _n  -> [ ]

       P.ECString s ->
          P.ETyped (P.EList [ P.ELit (P.ECNum (fromIntegral (fromEnum c))
                            P.CharLit) | c <- s ])
                   (P.TSeq P.TWild (P.TSeq (P.TNum 8) P.TBit))


-- | Infer the type of an expression with an explicit instantiation.
appTys :: P.Expr -> [Located (Maybe QName,Type)] -> Type -> InferM Expr
appTys expr ts tGoal =
  case expr of
    P.EVar x ->
      do res <- lookupVar x
         (e',t) <- case res of
           ExtVar s   -> instantiateWith (EVar x) s ts
           CurSCC e t -> instantiateWith e (Forall [] [] t) ts

         checkHasType e' t tGoal

    P.ELit l -> do e <- desugarLiteral False l
                   appTys e ts tGoal

    P.ECon ec -> do let s1 = typeOf ec
                    (e',t) <- instantiateWith (ECon ec) s1 ts
                    checkHasType e' t tGoal

    P.EAppT e fs ->
      do ps <- mapM inferTyParam fs
         appTys e (ps ++ ts) tGoal

    -- Here is an example of why this might be useful:
    -- f ` { x = T } where type T = ...
    P.EWhere e ds ->
      inferDs ds $ \ds1 -> do e1 <- appTys e ts tGoal
                              return (EWhere e1 ds1)
         -- XXX: Is there a scoping issue here?  I think not, but check.

    P.ELocated e r ->
      inRange r (appTys e ts tGoal)

    P.ETuple    {} -> mono
    P.ERecord   {} -> mono
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

  where mono = do e'     <- checkE expr tGoal
                  (ie,t) <- instantiateWith e' (Forall [] [] tGoal) ts
                  -- XXX seems weird to need to do this, as t should be the same
                  -- as tGoal
                  checkHasType ie t tGoal


inferTyParam :: P.TypeInst -> InferM (Located (Maybe QName, Type))
inferTyParam (P.NamedInst param) =
  do let loc = srcRange (P.name param)
     t <- inRange loc $ checkType (P.value param) Nothing
     return $ Located loc (Just (mkUnqual (thing (P.name param))), t)

inferTyParam (P.PosInst param) =
  do t   <- checkType param Nothing
     rng <- case getLoc param of
              Nothing -> curRange
              Just r  -> return r
     return Located { srcRange = rng, thing = (Nothing, t) }

checkTypeOfKind :: P.Type -> Kind -> InferM Type
checkTypeOfKind ty k = checkType ty (Just k)


-- | We use this when we want to ensure that the expr has exactly
-- (syntactically) the given type.
inferE :: Doc -> P.Expr -> InferM (Expr, Type)
inferE desc expr =
  do t  <- newType desc KType
     e1 <- checkE expr t
     return (e1,t)

-- | Infer the type of an expression, and translate it to a fully elaborated
-- core term.
checkE :: P.Expr -> Type -> InferM Expr
checkE expr tGoal =
  case expr of
    P.EVar x ->
      do res <- lookupVar x
         (e',t) <- case res of
           ExtVar s   -> instantiateWith (EVar x) s []
           CurSCC e t -> return (e, t)

         checkHasType e' t tGoal

    P.ELit l -> (`checkE` tGoal) =<< desugarLiteral False l

    P.ECon ec ->
      do let s1 = typeOf ec
         (e',t) <- instantiateWith (ECon ec) s1 []
         checkHasType e' t tGoal

    P.ETuple es ->
      do etys <- expectTuple (length es) tGoal
         es'  <- zipWithM checkE es etys
         return (ETuple es')

    P.ERecord fs ->
      do (ns,es,ts) <- unzip3 `fmap` expectRec fs tGoal
         es' <- zipWithM checkE es ts
         return (ERec (zip ns es'))

    P.ESel e l ->
      do let src = case l of
                     RecordSel _ _ -> text "type of record"
                     TupleSel _ _  -> text "type of tuple"
                     ListSel _ _   -> text "type of sequence"
         (e',t) <- inferE src e
         f <- newHasGoal l t tGoal
         return (f e')

    P.EList [] ->
      do (len,a) <- expectSeq tGoal
         expectFin 0 len
         return (EList [] a)

    P.EList es ->
      do (len,a) <- expectSeq tGoal
         expectFin (length es) len
         es' <- mapM (`checkE` a) es
         return (EList es' a)

    P.EFromTo t1 Nothing Nothing ->
      do rng <- curRange
         bit <- newType (text "bit-width of enumeration sequnce") KNum
         fstT <- checkTypeOfKind t1 KNum
         let totLen = tNum (2::Int) .^. bit
             lstT   = totLen .-. tNum (1::Int)

         appTys (P.ECon ECFromTo)
           [ Located rng (Just (mkUnqual (Name x)), y)
           | (x,y) <- [ ("first",fstT), ("last", lstT), ("bits", bit) ]
           ] tGoal

    P.EFromTo t1 mbt2 mbt3 ->
      do l <- curRange
         let (c,fs) =
               case (mbt2, mbt3) of

                 (Nothing, Nothing) -> tcPanic "checkE"
                                        [ "EFromTo _ Nothing Nothing" ]
                 (Just t2, Nothing) ->
                    (ECFromThen, [ ("next", t2) ])

                 (Nothing, Just t3) ->
                    (ECFromTo, [ ("last", t3) ])

                 (Just t2, Just t3) ->
                    (ECFromThenTo, [ ("next",t2), ("last",t3) ])

         let e' = P.EAppT (P.ECon c)
                  [ P.NamedInst P.Named { name = Located l (Name x), value = y }
                  | (x,y) <- ("first",t1) : fs
                  ]

         checkE e' tGoal

    P.EInfFrom e1 Nothing ->
      checkE (P.EApp (P.ECon ECInfFrom) e1) tGoal

    P.EInfFrom e1 (Just e2) ->
      checkE (P.EApp (P.EApp (P.ECon ECInfFromThen) e1) e2) tGoal

    P.EComp e mss ->
      do (mss', dss, ts) <- unzip3 `fmap` zipWithM inferCArm [ 1 .. ] mss
         (len,a)<- expectSeq tGoal

         newGoals CtComprehension =<< unify len =<< smallest ts

         ds     <- combineMaps dss
         e'     <- withMonoTypes ds (checkE e a)
         return (EComp tGoal e' mss')

    P.EAppT e fs ->
      do ts <- mapM inferTyParam fs
         appTys e ts tGoal

    P.EApp fun@(dropLoc -> P.EApp (dropLoc -> P.ECon c) _)
           arg@(dropLoc -> P.ELit l)
      | c `elem` [ ECShiftL, ECShiftR, ECRotL, ECRotR, ECAt, ECAtBack ] ->
        do newArg <- do l1 <- desugarLiteral True l
                        return $ case arg of
                                   P.ELocated _ pos -> P.ELocated l1 pos
                                   _ -> l1
           checkE (P.EApp fun newArg) tGoal

    P.EApp e1 e2 ->
      do t1  <- newType (text "argument to function") KType
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
         checkHasType e' tSig tGoal

    P.ETypeVal t ->
      do l <- curRange
         checkE (P.EAppT (P.ECon ECDemote)
                  [P.NamedInst
                   P.Named { name = Located l (Name "val"), value = t }]) tGoal

    P.EFun ps e -> checkFun (text "anonymous function") ps e tGoal

    P.ELocated e r  -> inRange r (checkE e tGoal)


expectSeq :: Type -> InferM (Type,Type)
expectSeq ty =
  case ty of

    TUser _ _ ty' ->
         expectSeq ty'

    TCon (TC TCSeq) [a,b] ->
         return (a,b)

    TVar _ ->
      do tys@(a,b) <- genTys
         newGoals CtExactType =<< unify (tSeq a b) ty
         return tys

    _ ->
      do tys@(a,b) <- genTys
         recordError (TypeMismatch (tSeq a b) ty)
         return tys
  where
  genTys =
    do a <- newType (text "size of the sequence") KNum
       b <- newType (text "type of sequence elements") KType
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
         newGoals CtExactType =<< unify (tTuple tys) ty
         return tys

    _ ->
      do tys <- genTys
         recordError (TypeMismatch (tTuple tys) ty)
         return tys

  where
  genTys =forM [ 0 .. n - 1 ] $ \ i ->
              let desc = text "type of"
                     <+> ordinal i
                     <+> text "tuple field"
               in newType desc KType

expectRec :: [P.Named a] -> Type -> InferM [(Name,a,Type)]
expectRec fs ty =
  case ty of

    TUser _ _ ty' ->
         expectRec fs ty'

    TRec ls | Just tys <- mapM checkField ls ->
         return tys

    _ ->
      do (tys,res) <- genTys
         case ty of
           TVar TVFree{} -> do ps <- unify (TRec tys) ty
                               newGoals CtExactType ps
           _ -> recordError (TypeMismatch (TRec tys) ty)
         return res

  where
  checkField (n,t) =
    do f <- find (\f -> thing (P.name f) == n) fs
       return (thing (P.name f), P.value f, t)

  genTys =
    do res <- forM fs $ \ f ->
             do let field = thing (P.name f)
                t <- newType (text "type of field" <+> quotes (pp field)) KType
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

    TVar TVFree{} ->
      do newGoals CtExactType =<< unify (tNum n) ty

    _ ->
         recordError (TypeMismatch (tNum n) ty)

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
             res  <- newType (text "result of function") KType
             case ty of
               TVar TVFree{} -> do ps <- unify (foldr tFun res args) ty
                                   newGoals CtExactType  ps
               _             -> recordError (TypeMismatch (foldr tFun res args) ty)
             return (reverse tys ++ args, res)

    | otherwise =
      return (reverse tys, ty)

  genArgs arity = forM [ 1 .. arity ] $ \ ix ->
                      newType (text "argument" <+> ordinal ix) KType


checkHasType :: Expr -> Type -> Type -> InferM Expr
checkHasType e inferredType givenType =
  do ps <- unify givenType inferredType
     case ps of
       [] -> return e
       _  -> newGoals CtExactType ps >> return (ECast e givenType)


checkFun :: Doc -> [P.Pattern] -> P.Expr -> Type -> InferM Expr
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
smallest []   = newType (text "length of list comprehension") KNum
smallest [t]  = return t
smallest ts   = do a <- newType (text "length of list comprehension") KNum
                   newGoals CtComprehension [ a =#= foldr1 tMin ts ]
                   return a


checkP :: Doc -> P.Pattern -> Type -> InferM (Located QName)
checkP desc p tGoal =
  do (x, t) <- inferP desc p
     ps <- unify tGoal (thing t)
     case ps of
       [] -> return (Located (srcRange t) x)
       _  -> tcPanic "checkP" [ "Unexpected constraints:", show ps ]

{-| Infer the type of a pattern.  Assumes that the pattern will be just
a variable. -}
inferP :: Doc -> P.Pattern -> InferM (QName, Located Type)
inferP desc pat =
  case pat of

    P.PVar x0 ->
      do a   <- newType desc KType
         let x = thing x0
         return (mkUnqual x, x0 { thing = a })

    P.PTyped p t ->
      do tSig <- checkTypeOfKind t KType
         ln   <- checkP desc p tSig
         return (thing ln, ln { thing = tSig })

    _ -> tcPanic "inferP" [ "Unexpected pattern:", show pat ]



-- | Infer the type of one match in a list comprehension.
inferMatch :: P.Match -> InferM (Match, QName, Located Type, Type)
inferMatch (P.Match p e) =
  do (x,t) <- inferP (text "XXX:MATCH") p
     n     <- newType (text "sequence length of comprehension match") KNum
     e'    <- checkE e (tSeq n (thing t))
     return (From x (thing t) e', x, t, n)

inferMatch (P.MatchLet b)
  | P.bMono b =
  do a <- newType (text "`let` binding in comprehension") KType
     b1 <- checkMonoB b a
     return (Let b1, dName b1, Located (srcRange (P.bName b)) a, tNum (1::Int))

  | otherwise = tcPanic "inferMatch"
                      [ "Unexpected polymorphic match let:", show b ]

-- | Infer the type of one arm of a list comprehension.
inferCArm :: Int -> [P.Match] -> InferM
              ( [Match]
              , Map QName (Located Type)-- defined vars
              , Type                    -- length of sequence
              )

inferCArm _ [] = do n <- newType (text "lenght of empty comprehension") KNum
                                                    -- shouldn't really happen
                    return ([], Map.empty, n)
inferCArm _ [m] =
  do (m1, x, t, n) <- inferMatch m
     return ([m1], Map.singleton x t, n)

inferCArm armNum (m : ms) =
  do (m1, x, t, n)  <- inferMatch m
     (ms', ds, n') <- withMonoType (x,t) (inferCArm armNum ms)
     -- XXX: Well, this is just the lenght of this sub-sequence
     let src = text "length of" <+> ordinal armNum <+>
                                  text "arm of list comprehension"
     sz <- newType src KNum
     newGoals CtComprehension [ sz =#= (n .*. n') ]
     return (m1 : ms', Map.insertWith (\_ old -> old) x t ds, sz)

-- | @inferBinds isTopLevel isRec binds@ performs inference for a
-- strongly-connected component of 'P.Bind's. If @isTopLevel@ is true,
-- any bindings without type signatures will be generalized. If it is
-- false, and the mono-binds flag is enabled, no bindings without type
-- signatures will be generalized, but bindings with signatures will
-- be unaffected.
inferBinds :: Bool -> Bool -> [P.Bind] -> InferM [Decl]
inferBinds isTopLevel isRec binds =
  mdo let exprMap = Map.fromList [ (x,inst (EVar x) (dDefinition b))
                                 | b <- genBs, let x = dName b ] -- REC.

          inst e (ETAbs x e1)     = inst (ETApp e (TVar (tpVar x))) e1
          inst e (EProofAbs _ e1) = inst (EProofApp e) e1
          inst e _                = e

      -- when mono-binds is enabled, and we're not checking top-level
      -- declarations, mark all bindings lacking signatures as monomorphic
      monoBinds <- getMonoBinds
      let binds' | monoBinds && not isTopLevel = sigs ++ monos
                 | otherwise                   = binds

          (sigs,noSigs) = partition (isJust . P.bSignature) binds
          monos         = [ b { P.bMono = True } | b <- noSigs ]


      ((doneBs, genCandidates), cs) <-
        collectGoals $

        {- Guess type is here, because while we check user supplied signatures
           we may generate additional constraints. For example, `x - y` would
           generate an additional constraint `x >= y`. -}
        do (newEnv,todos) <- unzip `fmap` mapM (guessType exprMap) binds'
           let extEnv = if isRec then withVarTypes newEnv else id

           extEnv $
             do let (sigsAndMonos,noSigGen) = partitionEithers todos
                genCs <- sequence noSigGen
                done  <- sequence sigsAndMonos
                simplifyAllConstraints
                return (done, genCs)
      genBs <- generalize genCandidates cs -- RECURSION
      return (doneBs ++ genBs)


{- | Come up with a type for recursive calls to a function, and decide
     how we are going to be checking the binding.
     Returns: (Name, type or schema, computation to check binding)

     The `exprMap` is a thunk where we can lookup the final expressions
     and we should be careful not to force it.
-}
guessType :: Map QName Expr -> P.Bind ->
              InferM ( (QName, VarType)
                     , Either (InferM Decl)    -- no generalization
                              (InferM Decl)    -- generalize these
                     )
guessType exprMap b@(P.Bind { .. }) =
  case bSignature of

    Just s ->
      do s1 <- checkSchema s
         return ((name, ExtVar (fst s1)), Left (checkSigB b s1))

    Nothing
      | bMono ->
         do t <- newType (text "defintion of" <+> quotes (pp name)) KType
            let schema = Forall [] [] t
            return ((name, ExtVar schema), Left (checkMonoB b t))

      | otherwise ->

        do t <- newType (text "definition of" <+> quotes (pp name)) KType
           let noWay = tcPanic "guessType" [ "Missing expression for:" ,
                                                                show name ]
               expr  = Map.findWithDefault noWay name exprMap

           return ((name, CurSCC expr t), Right (checkMonoB b t))
  where
  name = thing bName


-- | Try to evaluate the inferred type of a mono-binding
simpMonoBind :: Decl -> Decl
simpMonoBind d =
  case dSignature d of
    Forall [] [] t ->
      let t1 = simpType t
      in if t == t1 then d else d { dSignature  = Forall [] [] t1
                                  , dDefinition = ECast (dDefinition d) t1
                                  }
    _ -> d


-- | The inputs should be declarations with monomorphic types
-- (i.e., of the form `Forall [] [] t`).
generalize :: [Decl] -> [Goal] -> InferM [Decl]

{- This may happen because we have monomorphic bindings.
In this case we may get some goal, due to the monomorphic bindings,
but the group of components is empty. -}
generalize [] gs0 =
  do addGoals gs0
     return []


generalize bs0 gs0 =
  do gs <- forM gs0 $ \g -> applySubst g

     -- XXX: Why would these bindings have signatures??
     bs1 <- forM bs0 $ \b -> do s <- applySubst (dSignature b)
                                return b { dSignature = s }

     let bs = map simpMonoBind bs1

     let goalFVS g  = Set.filter isFreeTV $ fvs $ goal g
         inGoals    = Set.unions $ map goalFVS gs
         inSigs     = Set.filter isFreeTV $ fvs $ map dSignature bs
         candidates = Set.union inGoals inSigs


     asmpVs <- varsWithAsmps



     let gen0          = Set.difference candidates asmpVs
         stays g       = any (`Set.member` gen0) $ Set.toList $ goalFVS g
         (here0,later) = partition stays gs

     -- Figure our what might be ambigious
     let (maybeAmbig, ambig) = partition ((KNum ==) . kindOf)
                             $ Set.toList
                             $ Set.difference gen0 inSigs

     when (not (null ambig)) $ recordError $ AmbiguousType $ map dName bs

     cfg <- getSolverConfig
     (as0,here1,defSu,ws) <- io $ improveByDefaulting cfg maybeAmbig here0
     mapM_ recordWarning ws
     let here = map goal here1

     let as     = as0 ++ Set.toList (Set.difference inSigs asmpVs)
         asPs   = [ TParam { tpUnique = x, tpKind = k, tpName = Nothing }
                                                   | TVFree x k _ _ <- as ]
     totSu <- getSubst
     let
         su     = listSubst (zip as (map (TVar . tpVar) asPs)) @@ defSu @@ totSu
         qs     = map (apSubst su) here

         genE e = foldr ETAbs (foldr EProofAbs (apSubst su e) qs) asPs
         genB d = d { dDefinition = genE (dDefinition d)
                    , dSignature  = Forall asPs qs
                                  $ simpType $ apSubst su $ sType $ dSignature d
                    }

     addGoals later
     return (map genB bs)




checkMonoB :: P.Bind -> Type -> InferM Decl
checkMonoB b t =
  inRangeMb (getLoc b) $
  do e1 <- checkFun (pp (thing (P.bName b))) (P.bParams b) (P.bDef b) t
     let f = thing (P.bName b)
     return Decl { dName = f
                 , dSignature = Forall [] [] t
                 , dDefinition = e1
                 , dPragmas = P.bPragmas b
                 }

-- XXX: Do we really need to do the defaulting business in two different places?
checkSigB :: P.Bind -> (Schema,[Goal]) -> InferM Decl
checkSigB b (Forall as asmps0 t0, validSchema) =
  inRangeMb (getLoc b) $
  withTParams as $
  do (e1,cs0) <- collectGoals $
                do e1 <- checkFun (pp (thing (P.bName b))) (P.bParams b) (P.bDef b) t0
                   () <- simplifyAllConstraints  -- XXX: using `asmps` also...
                   return e1
     cs <- applySubst cs0

     let letGo qs c  = Set.null (qs `Set.intersection` fvs (goal c))

         splitPreds qs n ps =
           let (l,n1) = partition (letGo qs) ps
           in if null n1
                then (l,n)
                else splitPreds (fvs (map goal n1) `Set.union` qs) (n1 ++ n) l

         (later0,now) = splitPreds (Set.fromList (map tpVar as)) [] cs

     asmps1 <- applySubst asmps0

     defSu1 <- proveImplication (P.bName b) as asmps1 (validSchema ++ now)
     let later = apSubst defSu1 later0
         asmps = apSubst defSu1 asmps1

     -- Now we check for any remaining variables that are not mentioned
     -- in the environment.  The plan is to try to default these to something
     -- reasonable.
     do let laterVs = fvs (map goal later)
        asmpVs <- varsWithAsmps
        let genVs   = laterVs `Set.difference` asmpVs
            (maybeAmbig,ambig) = partition ((== KNum) . kindOf)
                                           (Set.toList genVs)
        when (not (null ambig)) $ recordError
                                $ AmbiguousType [ thing (P.bName b) ]

        cfg <- getSolverConfig
        (_,_,defSu2,ws) <- io $ improveByDefaulting cfg maybeAmbig later
        mapM_ recordWarning ws
        extendSubst defSu2

     addGoals later

     su <- getSubst
     let su' = defSu1 @@ su
         t   = apSubst su' t0
         e2  = apSubst su' e1

     return Decl
        { dName       = thing (P.bName b)
        , dSignature  = Forall as asmps $ simpType t
        , dDefinition = foldr ETAbs (foldr EProofAbs e2 asmps) as
        , dPragmas    = P.bPragmas b
        }

inferDs :: FromDecl d => [d] -> ([DeclGroup] -> InferM a) -> InferM a
inferDs ds continue = checkTyDecls =<< orderTyDecls (mapMaybe toTyDecl ds)
  where
  isTopLevel = isTopDecl (head ds)

  checkTyDecls (TS t : ts) =
    do t1 <- checkTySyn t
       withTySyn t1 (checkTyDecls ts)

  checkTyDecls (NT t : ts) =
    do t1 <- checkNewtype t
       withNewtype t1 (checkTyDecls ts)

  -- We checked all type synonyms, now continue with value-level definitions:
  checkTyDecls [] = checkBinds [] $ orderBinds $ mapMaybe toBind ds


  checkBinds decls (CyclicSCC bs : more) =
     do bs1 <- inferBinds isTopLevel True bs
        foldr (\b m -> withVar (dName b) (dSignature b) m)
              (checkBinds (Recursive bs1 : decls) more)
              bs1

  checkBinds decls (AcyclicSCC c : more) =
    do [b] <- inferBinds isTopLevel False [c]
       withVar (dName b) (dSignature b) $
         checkBinds (NonRecursive b : decls) more

  -- We are done with all value-level definitions.
  -- Now continue with anything that's in scope of the declarations.
  checkBinds decls [] = continue (reverse decls)

tcPanic :: String -> [String] -> a
tcPanic l msg = panic ("[TypeCheck] " ++ l) msg

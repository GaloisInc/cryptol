-- |
-- Module      :  Cryptol.Parser.NoPat
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- The purpose of this module is to convert all irrefutable patterns to variable
-- patterns.  It also eliminates pattern bindings by de-sugaring them
-- into `Bind`.  Furthermore, here we associate signatures, fixities,
-- and pragmas with the names to which they belong.  We also merge
-- empty 'DForeign' binds with their cryptol implementations, if they
-- exist.

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BlockArguments #-}
module Cryptol.Parser.NoPat (RemovePatterns(..),Error(..)) where

import Cryptol.Parser.AST
import Cryptol.Parser.Position(Range(..),emptyRange,start,at)
import Cryptol.Parser.Names (namesP')
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.RecordMap

import           MonadLib hiding (mapM)
import           Data.Maybe(maybeToList)
import qualified Data.Map as Map
import           Data.Text (Text)

import GHC.Generics (Generic)
import Control.DeepSeq

class RemovePatterns t where
  -- | Eliminate all patterns in a program.
  removePatterns :: t -> (t, [Error])

instance RemovePatterns (Program PName) where
  removePatterns p = runNoPatM (noPatProg p)

instance RemovePatterns (Expr PName) where
  removePatterns e = runNoPatM (noPatE e)

instance RemovePatterns (ModuleG mname PName) where
  removePatterns m = runNoPatM (noPatModule m)

instance RemovePatterns [Decl PName] where
  removePatterns ds = runNoPatM (noPatDs ds)

instance RemovePatterns (NestedModule PName) where
  removePatterns (NestedModule m) = (NestedModule m1,errs)
    where (m1,errs) = removePatterns m

simpleBind :: Located PName -> Expr PName -> Bind PName
simpleBind x e = Bind { bName = x, bParams = noParams
                      , bDef = at e (Located emptyRange (exprDef e))
                      , bSignature = Nothing, bPragmas = []
                      , bMono = True, bInfix = False, bFixity = Nothing
                      , bDoc = Nothing
                      , bExport = Public
                      }

sel :: Pattern PName -> PName -> Selector -> Bind PName
sel p x s = let (a,ts) = splitSimpleP p
            in simpleBind a (at p (foldl ETyped (ESel (EVar x) s) ts))

-- | Given a pattern, transform it into a simple pattern and a set of bindings.
-- Simple patterns may only contain variables and type annotations.

-- XXX: We can replace the types in the selectors with annotations on the bindings.
noPat :: Bool -> Pattern PName -> NoPatM (Pattern PName, [Bind PName])
noPat conOk pat =
  case pat of
    PVar x -> return (PVar x, [])

    PCon c ps
      | conOk ->
        do (as,dss) <- mapAndUnzipM (noPat False) ps
           pure (PCon c as, concat dss)

      | otherwise ->
        do let r = srcRange c
           recordError (InvalidConstructorPattern r)
           x <- newName
           pure (pVar r x, [])

    PWild ->
      do x <- newName
         r <- getRange
         return (pVar r x, [])

    PTuple ps ->
      do (as,dss) <- unzip `fmap` mapM (noPat False) ps
         x <- newName
         r <- getRange
         let len      = length ps
             ty       = TTuple (replicate len TWild)
             getN a n = sel a x (TupleSel n (Just len))
         return (pTy r x ty, zipWith getN as [0..] ++ concat dss)

    PList [] ->
      do x <- newName
         r <- getRange
         return (pTy r x (TSeq (TNum 0) TWild), [])

    PList ps ->
      do (as,dss) <- unzip `fmap` mapM (noPat False) ps
         x <- newName
         r <- getRange
         let len      = length ps
             ty       = TSeq (TNum (toInteger len)) TWild
             getN a n = sel a x (ListSel n (Just len))
         return (pTy r x ty, zipWith getN as [0..] ++ concat dss)

    PRecord fs ->
      do let (shape, els) = unzip (canonicalFields fs)
         (as,dss) <- unzip `fmap` mapM (noPat False . snd) els
         x <- newName
         r <- getRange
         let ty           = TRecord (fmap (\(rng,_) -> (rng,TWild)) fs)
             getN a n     = sel a x (RecordSel n (Just shape))
         return (pTy r x ty, zipWith getN as shape ++ concat dss)

    PTyped p t ->
      do (a,ds) <- noPat conOk p
         return (PTyped a t, ds)

    -- XXX: We can do more with type annotations here
    PSplit p1 p2 ->
      do (a1,ds1) <- noPat False p1
         (a2,ds2) <- noPat False p2
         x <- newName
         tmp <- newName
         r <- getRange
         let bTmp = simpleBind (Located r tmp) (ESplit (EVar x))
             b1   = sel a1 tmp (TupleSel 0 (Just 2))
             b2   = sel a2 tmp (TupleSel 1 (Just 2))
         return (pVar r x, bTmp : b1 : b2 : ds1 ++ ds2)

    PLocated p r1 -> inRange r1 (noPat conOk p)

  where
  pVar r x   = PVar (Located r x)
  pTy  r x   = PTyped (PVar (Located r x))


splitSimpleP :: Pattern PName -> (Located PName, [Type PName])
splitSimpleP (PVar x)     = (x, [])
splitSimpleP (PTyped p t) = let (x,ts) = splitSimpleP p
                            in (x, t:ts)
splitSimpleP p            = panic "splitSimpleP"
                                  [ "Non-simple pattern", show p ]

--------------------------------------------------------------------------------

noPatE :: Expr PName -> NoPatM (Expr PName)
noPatE expr =
  case expr of
    EVar {}       -> return expr
    ELit {}       -> return expr
    EGenerate e   -> EGenerate <$> noPatE e
    ETuple es     -> ETuple  <$> mapM noPatE es
    ERecord es    -> ERecord <$> traverse (traverse noPatE) es
    ESel e s      -> ESel    <$> noPatE e <*> return s
    EUpd mb fs    -> EUpd    <$> traverse noPatE mb <*> traverse noPatUF fs
    EList es      -> EList   <$> mapM noPatE es
    EFromTo {}    -> return expr
    EFromToBy {}  -> return expr
    EFromToDownBy {} -> return expr
    EFromToLessThan{} -> return expr
    EInfFrom e e' -> EInfFrom <$> noPatE e <*> traverse noPatE e'
    EComp e mss   -> EComp  <$> noPatE e <*> mapM noPatArm mss
    EApp e1 e2    -> EApp   <$> noPatE e1 <*> noPatE e2
    EAppT e ts    -> EAppT  <$> noPatE e <*> return ts
    EIf e1 e2 e3  -> EIf    <$> noPatE e1 <*> noPatE e2 <*> noPatE e3
    ECase e as    -> ECase  <$> noPatE e  <*> traverse noPatAlt as
    EWhere e ds   -> EWhere <$> noPatE e <*> noPatDs ds
    ETyped e t    -> ETyped <$> noPatE e <*> return t
    ETypeVal {}   -> return expr
    EFun desc ps e -> noPatFun (funDescrName desc) (funDescrArgOffset desc) ps e
    ELocated e r1 -> ELocated <$> inRange r1 (noPatE e) <*> return r1

    ESplit e      -> ESplit  <$> noPatE e
    EParens e     -> EParens <$> noPatE e
    EInfix x y f z-> EInfix  <$> noPatE x <*> pure y <*> pure f <*> noPatE z
    EPrefix op e  -> EPrefix op <$> noPatE e

noPatAlt :: CaseAlt PName -> NoPatM (CaseAlt PName)
noPatAlt (CaseAlt p e) =
  do (p1,ds) <- noPat True p
     e1 <- noPatE e
     let e2 = case ds of
                [] -> e1
                _  -> EWhere e1 (map DBind ds)
     pure (CaseAlt p1 e2)

noPatUF :: UpdField PName -> NoPatM (UpdField PName)
noPatUF (UpdField h ls e) = UpdField h ls <$> noPatE e

-- Desugar lambdas with multiple patterns into a sequence of
-- lambdas with a single, simple pattern each.  Bindings required
-- to simplify patterns are placed inside "where" blocks that are
-- interspersed into the lambdas to ensure that the lexical
-- structure is reliable, with names on the right shadowing names
-- on the left.
noPatFun :: Maybe PName -> Int -> [Pattern PName] -> Expr PName -> NoPatM (Expr PName)
noPatFun _   _      []     e = noPatE e
noPatFun mnm offset (p:ps) e =
  do (p',ds) <- noPat False p
     e' <- noPatFun mnm (offset+1) ps e
     let body = case ds of
                  [] -> e'
                  _  -> EWhere e' $ map DBind (reverse ds)
                           --                  ^
                           -- This reverse isn't strictly necessary, but yields more sensible
                           -- variable ordering results from type inference.  I'm not entirely
                           -- sure why.
     let desc = FunDesc mnm offset
     return (EFun desc [p'] body)

noPatArm :: [Match PName] -> NoPatM [Match PName]
noPatArm ms = concat <$> mapM noPatM ms

noPatM :: Match PName -> NoPatM [Match PName]
noPatM (Match p e) =
  do (x,bs) <- noPat False p
     e1     <- noPatE e
     return (Match x e1 : map MatchLet bs)
noPatM (MatchLet b) = (return . MatchLet) <$> noMatchB b

noMatchB :: Bind PName -> NoPatM (Bind PName)
noMatchB b =
  case thing (bDef b) of

    DPrim | null (bindParams b) -> return b
          | otherwise        -> panic "NoPat" [ "noMatchB: primitive with params"
                                              , show b ]

    DForeign _ Nothing
      | null (bindParams b) -> return b
      | otherwise        -> panic "NoPat" [ "noMatchB: foreign with params"
                                          , show b ]

    DForeign cc (Just i) -> noMatchI (DForeign cc . Just) i

    DImpl i -> noMatchI DImpl i

  where
  noMatchI def i =
    do i' <- case i of
               DExpr e ->
                 DExpr <$> noPatFun (Just (thing (bName b))) 0 (bindParams b) e
               DPropGuards guards ->
                 let nm = thing (bName b)
                     ps = bindParams b
                 in  DPropGuards <$> mapM (noPatPropGuardCase nm ps) guards
       pure b { bParams = dropParams (bParams b), bDef = def i' <$ bDef b }

noPatPropGuardCase ::
  PName ->
  [Pattern PName] ->
  PropGuardCase PName -> NoPatM (PropGuardCase PName)
noPatPropGuardCase f xs pc =
  do e <- noPatFun (Just f) 0 xs (pgcExpr pc)
     pure pc { pgcExpr = e }

noMatchD :: Decl PName -> NoPatM [Decl PName]
noMatchD decl =
  case decl of
    DSignature {}   -> return [decl]
    DPragma {}      -> return [decl]
    DFixity{}       -> return [decl]

    DBind b         -> do b1 <- noMatchB b
                          return [DBind b1]
    DRec {}         -> panic "noMatchD" [ "DRec" ]

    DPatBind p e    -> do (p',bs) <- noPat False p
                          let (x,ts) = splitSimpleP p'
                          e1 <- noPatE e
                          let e2 = foldl ETyped e1 ts
                          return $ DBind Bind { bName = x
                                              , bParams = noParams
                                              , bDef = at e (Located emptyRange (exprDef e2))
                                              , bSignature = Nothing
                                              , bPragmas = []
                                              , bMono = False
                                              , bInfix = False
                                              , bFixity = Nothing
                                              , bDoc = Nothing
                                              , bExport = Public
                                              } : map DBind bs
    DType {}        -> return [decl]
    DProp {}        -> return [decl]

    DLocated d r1   -> do bs <- inRange r1 $ noMatchD d
                          return $ map (`DLocated` r1) bs

noPatDs :: [Decl PName] -> NoPatM [Decl PName]
noPatDs ds =
  do ds1 <- concat <$> mapM noMatchD ds
     let fixes = Map.fromListWith (++) $ concatMap toFixity ds1
         amap = AnnotMap
           { annPragmas  = Map.fromListWith (++) $ concatMap toPragma ds1
           , annSigs     = Map.fromListWith (++) $ concatMap toSig ds1
           , annValueFs  = fixes
           , annTypeFs   = fixes
           , annDocs     = Map.empty
             -- There shouldn't be any foreigns at non-top-level
           , annForeigns = Map.empty
           }

     (ds2, AnnotMap { .. }) <- runStateT amap (annotDs ds1)

     forM_ (Map.toList annPragmas) $ \(n,ps) ->
       forM_ ps $ \p -> recordError $ PragmaNoBind (p { thing = n }) (thing p)

     forM_ (Map.toList annSigs) $ \(n,ss) ->
       do _ <- checkSigs n ss
          forM_ ss $ \s -> recordError $ SignatureNoBind (s { thing = n })
                                                         (thing s)

     -- Generate an error if a fixity declaration is not used for
     -- either a value-level or type-level operator.
     forM_ (Map.toList (Map.intersection annValueFs annTypeFs)) $ \(n,fs) ->
       forM_ fs $ \f -> recordError $ FixityNoBind f { thing = n }

     return ds2



noPatTopDs :: [TopDecl PName] -> NoPatM [TopDecl PName]
noPatTopDs tds =
  do desugared <- concat <$> mapM desugar tds

     let allDecls  = map tlValue (decls desugared)
         fixes     = Map.fromListWith (++) $ concatMap toFixity allDecls

     let ann = AnnotMap
           { annPragmas  = Map.fromListWith (++) $ concatMap toPragma allDecls
           , annSigs     = Map.fromListWith (++) $ concatMap toSig    allDecls
           , annValueFs  = fixes
           , annTypeFs   = fixes
           , annDocs     = Map.fromListWith (++) $ concatMap toDocs $ decls tds
           , annForeigns = Map.fromListWith (<>) $ concatMap toForeigns allDecls
          }

     (tds', AnnotMap { .. }) <- runStateT ann (annotTopDs desugared)

     forM_ (Map.toList annPragmas) $ \(n,ps) ->
       forM_ ps $ \p -> recordError $ PragmaNoBind (p { thing = n }) (thing p)

     forM_ (Map.toList annSigs) $ \(n,ss) ->
       do _ <- checkSigs n ss
          forM_ ss $ \s -> recordError $ SignatureNoBind (s { thing = n })
                                                         (thing s)

     -- Generate an error if a fixity declaration is not used for
     -- either a value-level or type-level operator.
     forM_ (Map.toList (Map.intersection annValueFs annTypeFs)) $ \(n,fs) ->
       forM_ fs $ \f -> recordError $ FixityNoBind f { thing = n }

     return tds'

  where
  decls xs = [ d | Decl d <- xs ]

  desugar d =
    case d of
      Decl tl -> do ds <- noMatchD (tlValue tl)
                    return [ Decl tl { tlValue = d1 } | d1 <- ds ]
      x      -> return [x]


noPatProg :: Program PName -> NoPatM (Program PName)
noPatProg (Program topDs) = Program <$> noPatTopDs topDs

noPatModule :: ModuleG mname PName -> NoPatM (ModuleG mname PName)
noPatModule m =
  do def <-
       case mDef m of
         NormalModule ds -> NormalModule <$> noPatTopDs ds
         FunctorInstance f as i -> pure (FunctorInstance f as i)
         InterfaceModule s -> pure (InterfaceModule s)
     pure m { mDef = def }

--------------------------------------------------------------------------------

-- | For each binding name, does there exist an empty foreign bind, a normal
-- cryptol bind, or both.
data AnnForeign = OnlyForeign ForeignMode | OnlyImpl | BothForeignImpl ForeignMode

instance Semigroup AnnForeign where
  OnlyForeign cc     <> OnlyImpl           = BothForeignImpl cc
  OnlyImpl           <> OnlyForeign cc     = BothForeignImpl cc
  _                  <> BothForeignImpl cc = BothForeignImpl cc
  BothForeignImpl cc <> _                  = BothForeignImpl cc
  OnlyForeign cc     <> OnlyForeign _      = OnlyForeign cc
  OnlyImpl           <> OnlyImpl           = OnlyImpl

data AnnotMap = AnnotMap
  { annPragmas  :: Map.Map PName [Located  Pragma       ]
  , annSigs     :: Map.Map PName [Located (Schema PName)]
  , annValueFs  :: Map.Map PName [Located  Fixity       ]
  , annTypeFs   :: Map.Map PName [Located  Fixity       ]
  , annDocs     :: Map.Map PName [Located  Text         ]
  , annForeigns :: Map.Map PName AnnForeign
  }

type Annotates a = a -> StateT AnnotMap NoPatM a

-- | Add annotations to exported declaration groups.
--
-- XXX: This isn't quite right: if a signature and binding have different
-- export specifications, this will favor the specification of the binding.
-- This is most likely the intended behavior, so it's probably fine, but it does
-- smell a bit.
annotTopDs :: Annotates [TopDecl PName]
annotTopDs tds =
  case tds of

    d : ds ->
      case d of
        Decl d1 ->
          do ignore <- runExceptionT (annotD (tlValue d1))
             case ignore of
               Left _   -> annotTopDs ds
               Right d2 -> (Decl (d1 { tlValue = d2 }) :) <$> annotTopDs ds

        DPrimType tl ->
          do pt <- annotPrimType (tlValue tl)
             let d1 = DPrimType tl { tlValue = pt }
             (d1 :) <$> annotTopDs ds

        DParamDecl {} -> (d :) <$> annotTopDs ds
        DInterfaceConstraint {} -> (d :) <$> annotTopDs ds

        -- XXX: we may want to add pragmas to newtypes and enums?
        TDNewtype {} -> (d :) <$> annotTopDs ds
        TDEnum {}    -> (d :) <$> annotTopDs ds
        Include {}   -> (d :) <$> annotTopDs ds

        DModule m ->
          case removePatterns (tlValue m) of
            (m1,errs) -> do lift (mapM_ recordError errs)
                            (DModule m { tlValue = m1 } :) <$> annotTopDs ds

        DImport {} -> (d :) <$> annotTopDs ds

        DModParam {} -> (d :) <$> annotTopDs ds

    [] -> return []


-- | Add annotations, keeping track of which annotations are not yet used up.
annotDs :: Annotates [Decl PName]
annotDs (d : ds) =
  do ignore <- runExceptionT (annotD d)
     case ignore of
       Left ()   -> annotDs ds
       Right d1  -> (d1 :) <$> annotDs ds
annotDs [] = return []

-- | Add annotations, keeping track of which annotations are not yet used up.
-- The exception indicates which declarations are no longer needed.
annotD :: Decl PName -> ExceptionT () (StateT AnnotMap NoPatM) (Decl PName)
annotD decl =
  case decl of
    DBind b       -> DBind <$> annotB b
    DRec {}       -> panic "annotD" [ "DRec" ]
    DSignature {} -> raise ()
    DFixity{}     -> raise ()
    DPragma {}    -> raise ()
    DPatBind {}   -> raise ()
    DType tysyn   -> DType <$> lift (annotTySyn tysyn)
    DProp propsyn -> DProp <$> lift (annotPropSyn propsyn)
    DLocated d r  -> (`DLocated` r) <$> annotD d

-- | Add pragma/signature annotations to a binding.
-- Also perform de-duplication of empty 'DForeign' binds generated by the parser
-- if there exists a cryptol implementation.
-- The exception indicates which declarations are no longer needed.
annotB :: Bind PName -> ExceptionT () (StateT AnnotMap NoPatM) (Bind PName)
annotB Bind { .. } =
  do AnnotMap { .. } <- get
     let name       = thing bName
         remove _ _ = Nothing
         (thisPs    , ps') = Map.updateLookupWithKey remove name annPragmas
         (thisSigs  , ss') = Map.updateLookupWithKey remove name annSigs
         (thisFixes , fs') = Map.updateLookupWithKey remove name annValueFs
         (thisDocs  , ds') = Map.updateLookupWithKey remove name annDocs
         thisForeign       = Map.lookup name annForeigns
     -- Compute the new def before updating the state, since we don't want to
     -- consume the annotations if we are throwing away an empty foreign def.
     def' <- case thisForeign of
               Just (BothForeignImpl cc)
                 | DForeign _ _ <- thing bDef -> raise ()
                 | DImpl i    <- thing bDef -> pure (DForeign cc (Just i) <$ bDef)
               _ -> pure bDef
     s <- lift $ lift $ checkSigs name $ jn thisSigs
     f <- lift $ lift $ checkFixs name $ jn thisFixes
     d <- lift $ lift $ checkDocs name $ jn thisDocs
     set AnnotMap { annPragmas = ps'
                  , annSigs    = ss'
                  , annValueFs = fs'
                  , annDocs    = ds'
                  , ..
                  }
     return Bind { bSignature = s
                 , bDef = def'
                 , bPragmas = map thing (jn thisPs) ++ bPragmas
                 , bFixity = f
                 , bDoc = d
                 , ..
                 }
  where jn x = concat (maybeToList x)

annotTyThing :: PName -> StateT AnnotMap NoPatM (Maybe Fixity)
annotTyThing name =
  do AnnotMap { .. } <- get
     let remove _ _ = Nothing
         (thisFixes, ts') = Map.updateLookupWithKey remove name annTypeFs
     f <- lift $ checkFixs name $ concat $ maybeToList thisFixes
     set AnnotMap { annTypeFs = ts', .. }
     pure f


-- | Add fixity annotations to a type synonym binding.
annotTySyn :: Annotates (TySyn PName)
annotTySyn (TySyn ln _ params rhs) =
  do f <- annotTyThing (thing ln)
     pure (TySyn ln f params rhs)

-- | Add fixity annotations to a constraint synonym binding.
annotPropSyn :: Annotates (PropSyn PName)
annotPropSyn (PropSyn ln _ params rhs) =
  do f <- annotTyThing (thing ln)
     pure (PropSyn ln f params rhs)

-- | Annotate a primitive type declaration.
annotPrimType :: Annotates (PrimType PName)
annotPrimType pt =
  do f <- annotTyThing (thing (primTName pt))
     pure pt { primTFixity = f }

-- | Check for multiple signatures.
checkSigs :: PName -> [Located (Schema PName)] -> NoPatM (Maybe (Schema PName))
checkSigs _ []             = return Nothing
checkSigs _ [s]            = return (Just (thing s))
checkSigs f xs@(s : _ : _) = do recordError $ MultipleSignatures f xs
                                return (Just (thing s))

checkFixs :: PName -> [Located Fixity] -> NoPatM (Maybe Fixity)
checkFixs _ []       = return Nothing
checkFixs _ [f]      = return (Just (thing f))
checkFixs f fs@(x:_) = do recordError $ MultipleFixities f $ map srcRange fs
                          return (Just (thing x))


checkDocs :: PName -> [Located Text] -> NoPatM (Maybe (Located Text))
checkDocs _ []       = return Nothing
checkDocs _ [d]      = return (Just d)
checkDocs f ds@(d:_) = do recordError $ MultipleDocs f (map srcRange ds)
                          return (Just d)


-- | Does this declaration provide some signatures?
toSig :: Decl PName -> [(PName, [Located (Schema PName)])]
toSig (DLocated d _)      = toSig d
toSig (DSignature xs s)   = [ (thing x,[Located (srcRange x) s]) | x <- xs ]
toSig _                   = []

-- | Does this declaration provide some signatures?
toPragma :: Decl PName -> [(PName, [Located Pragma])]
toPragma (DLocated d _)   = toPragma d
toPragma (DPragma xs s)   = [ (thing x,[Located (srcRange x) s]) | x <- xs ]
toPragma _                = []

-- | Does this declaration provide fixity information?
toFixity :: Decl PName -> [(PName, [Located Fixity])]
toFixity (DFixity f ns) = [ (thing n, [Located (srcRange n) f]) | n <- ns ]
toFixity _              = []

-- | Does this top-level declaration provide a documentation string?
toDocs :: TopLevel (Decl PName) -> [(PName, [Located Text])]
toDocs TopLevel { .. }
  | Just txt <- tlDoc = go txt tlValue
  | otherwise = []
  where
  go txt decl =
    case decl of
      DSignature ns _ -> [ (thing n, [txt]) | n <- ns ]
      DFixity _ ns    -> [ (thing n, [txt]) | n <- ns ]
      DBind b         -> [ (thing (bName b), [txt]) ]
      DRec {}         -> panic "toDocs" [ "DRec" ]
      DLocated d _    -> go txt d
      DPatBind p _    -> [ (thing n, [txt]) | n <- namesP' p ]

      -- XXX revisit these
      DPragma _ _     -> []
      DType _         -> []
      DProp _         -> []

-- | Is this declaration a foreign or regular bind?
toForeigns :: Decl PName -> [(PName, AnnForeign)]
toForeigns (DLocated d _) = toForeigns d
toForeigns (DBind Bind {..})
  | DForeign cc Nothing <- thing bDef = [ (thing bName, OnlyForeign cc) ]
  | DImpl _          <- thing bDef = [ (thing bName, OnlyImpl) ]
toForeigns _ = []

--------------------------------------------------------------------------------
newtype NoPatM a = M { unM :: ReaderT Range (StateT RW Id) a }

data RW     = RW { names :: !Int, errors :: [Error] }

data Error  = MultipleSignatures PName [Located (Schema PName)]
            | SignatureNoBind (Located PName) (Schema PName)
            | PragmaNoBind (Located PName) Pragma
            | MultipleFixities PName [Range]
            | FixityNoBind (Located PName)
            | MultipleDocs PName [Range]
            | InvalidConstructorPattern Range
              deriving (Show,Generic, NFData)

instance Functor NoPatM where fmap = liftM
instance Applicative NoPatM where
  pure x = M (pure x)
  (<*>) = ap
instance Monad NoPatM where
  return    = pure
  M x >>= k = M (x >>= unM . k)

-- | Pick a new name, to be used when desugaring patterns.
newName :: NoPatM PName
newName = M $ sets $ \s -> let x = names s
                           in (NewName NoPat x, s { names = x + 1 })

-- | Record an error.
recordError :: Error -> NoPatM ()
recordError e = M $ sets_ $ \s -> s { errors = e : errors s }

getRange :: NoPatM Range
getRange = M ask

inRange :: Range -> NoPatM a -> NoPatM a
inRange r m = M $ local r $ unM m


runNoPatM :: NoPatM a -> (a, [Error])
runNoPatM m
  = getErrs
  $ runId
  $ runStateT RW { names = 0, errors = [] }
  $ runReaderT (Range start start "")    -- hm
  $ unM m
  where getErrs (a,rw) = (a, errors rw)

--------------------------------------------------------------------------------

instance PP Error where
  ppPrec _ err =
    case err of
      MultipleSignatures x ss ->
        text "Multiple type signatures for" <+> quotes (pp x)
        $$ indent 2 (vcat (map pp ss))

      SignatureNoBind x s ->
        text "At" <+> pp (srcRange x) <.> colon <+>
        text "Type signature without a matching binding:"
         $$ indent 2 (pp (thing x) <+> colon <+> pp s)

      PragmaNoBind x s ->
        text "At" <+> pp (srcRange x) <.> colon <+>
        text "Pragma without a matching binding:"
         $$ indent 2 (pp s)

      MultipleFixities n locs ->
        text "Multiple fixity declarations for" <+> quotes (pp n)
        $$ indent 2 (vcat (map pp locs))

      FixityNoBind n ->
        text "At" <+> pp (srcRange n) <.> colon <+>
        text "Fixity declaration without a matching binding for:" <+>
         pp (thing n)

      MultipleDocs n locs ->
        text "Multiple documentation blocks given for:" <+> pp n
        $$ indent 2 (vcat (map pp locs))

      InvalidConstructorPattern r ->
        "At" <+> pp r <.> colon <+> "Invalid constructor pattern"
         $$ indent 2 "Constructors may appear only at the top level of a case."



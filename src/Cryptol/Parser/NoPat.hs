-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- The purpose of this module is to convert all patterns to variable
-- patterns.  It also eliminates pattern bindings by de-sugaring them
-- into `Bind`.  Furthermore, here we associate signatures and pragmas
-- with the names to which they belong.
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.Parser.NoPat (RemovePatterns(..),Error(..)) where

import Cryptol.Prims.Syntax
import Cryptol.Parser.AST
import Cryptol.Parser.Position(Range(..),start)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

import           MonadLib
import           Data.Maybe(maybeToList)
import           Data.Either(partitionEithers)
import qualified Data.Map as Map

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative(Applicative(..),(<$>))
import           Data.Traversable(traverse)
#endif

class RemovePatterns t where
  -- | Eliminate all patterns in a program.
  removePatterns :: t -> (t, [Error])

instance RemovePatterns Program where
  removePatterns p = runNoPatM (noPatProg p)

instance RemovePatterns Expr where
  removePatterns e = runNoPatM (noPatE e)

instance RemovePatterns Module where
  removePatterns m = runNoPatM (noPatModule m)

instance RemovePatterns [Decl] where
  removePatterns ds = runNoPatM (noPatDs ds)

simpleBind :: Located QName -> Expr -> Bind
simpleBind x e = Bind { bName = x, bParams = [], bDef = e
                      , bSignature = Nothing, bPragmas = []
                      , bMono = True
                      }

sel :: Pattern -> QName -> Selector -> Bind
sel p x s = let (a,ts) = splitSimpleP p
            in simpleBind a (foldl ETyped (ESel (EVar x) s) ts)

-- | Given a pattern, transform it into a simple pattern and a set of bindings.
-- Simple patterns may only contain variables and type annotations.

-- XXX: We can replace the types in the selcetors with annotations on the bindings.
noPat :: Pattern -> NoPatM (Pattern, [Bind])
noPat pat =
  case pat of
    PVar x -> return (PVar x, [])

    PWild ->
      do x <- newName
         r <- getRange
         return (pVar r x, [])

    PTuple ps ->
      do (as,dss) <- unzip `fmap` mapM noPat ps
         x <- newName
         r <- getRange
         let qx       = mkUnqual x
         let len      = length ps
             ty       = TTuple (replicate len TWild)
             getN a n = sel a qx (TupleSel n (Just len))
         return (pTy r x ty, zipWith getN as [0..] ++ concat dss)

    PList [] ->
      do x <- newName
         r <- getRange
         return (pTy r x (TSeq (TNum 0) TWild), [])

    PList ps ->
      do (as,dss) <- unzip `fmap` mapM noPat ps
         x <- newName
         r <- getRange
         let qx       = mkUnqual x
             len      = length ps
             ty       = TSeq (TNum (fromIntegral len)) TWild
             getN a n = sel a qx (ListSel n (Just len))
         return (pTy r x ty, zipWith getN as [0..] ++ concat dss)

    PRecord fs ->
      do (as,dss) <- unzip `fmap` mapM (noPat . value) fs
         x <- newName
         r <- getRange
         let qx       = mkUnqual x
             shape    = map (thing . name) fs
             ty       = TRecord (map (fmap (\_ -> TWild)) fs)
             getN a n = sel a qx (RecordSel n (Just shape))
         return (pTy r x ty, zipWith getN as shape ++ concat dss)

    PTyped p t ->
      do (a,ds) <- noPat p
         return (PTyped a t, ds)

    -- XXX: Ww can do more with type annotations here
    PSplit p1 p2 ->
      do (a1,ds1) <- noPat p1
         (a2,ds2) <- noPat p2
         x <- newName
         tmp <- newName
         r <- getRange
         let qx   = mkUnqual x
             qtmp = mkUnqual tmp
             bTmp = simpleBind (Located r qtmp) (EApp (ECon ECSplitAt) (EVar qx))
             b1   = sel a1 qtmp (TupleSel 0 (Just 2))
             b2   = sel a2 qtmp (TupleSel 1 (Just 2))
         return (pVar r x, bTmp : b1 : b2 : ds1 ++ ds2)

    PLocated p r1 -> inRange r1 (noPat p)

  where
  pVar r x   = PVar (Located r x)
  pTy  r x t = PTyped (PVar (Located r x)) t


splitSimpleP :: Pattern -> (Located QName, [Type])
splitSimpleP (PVar x)     = (fmap mkUnqual x, [])
splitSimpleP (PTyped p t) = let (x,ts) = splitSimpleP p
                            in (x, t:ts)
splitSimpleP p            = panic "splitSimpleP"
                                  [ "Non-simple pattern", show p ]

--------------------------------------------------------------------------------

noPatE :: Expr -> NoPatM Expr
noPatE expr =
  case expr of
    EVar {}       -> return expr
    ECon {}       -> return expr
    ELit {}       -> return expr
    ETuple es     -> ETuple  <$> mapM noPatE es
    ERecord es    -> ERecord <$> mapM noPatF es
    ESel e s      -> ESel    <$> noPatE e <*> return s
    EList es      -> EList   <$> mapM noPatE es
    EFromTo {}    -> return expr
    EInfFrom e e' -> EInfFrom <$> noPatE e <*> traverse noPatE e'
    EComp e mss   -> EComp  <$> noPatE e <*> mapM noPatArm mss
    EApp e1 e2    -> EApp   <$> noPatE e1 <*> noPatE e2
    EAppT e ts    -> EAppT  <$> noPatE e <*> return ts
    EIf e1 e2 e3  -> EIf    <$> noPatE e1 <*> noPatE e2 <*> noPatE e3
    EWhere e ds   -> EWhere <$> noPatE e <*> noPatDs ds
    ETyped e t    -> ETyped <$> noPatE e <*> return t
    ETypeVal {}   -> return expr
    EFun ps e     -> do (ps1,e1) <- noPatFun ps e
                        return (EFun ps1 e1)
    ELocated e r1 -> ELocated <$> inRange r1 (noPatE e) <*> return r1

  where noPatF x = do e <- noPatE (value x)
                      return x { value = e }

noPatFun :: [Pattern] -> Expr -> NoPatM ([Pattern], Expr)
noPatFun ps e =
  do (xs,bs) <- unzip <$> mapM noPat ps
     e1 <- noPatE e
     let body = case concat bs of
                        [] -> e1
                        ds -> EWhere e1 $ map DBind ds
     return (xs, body)


noPatArm :: [Match] -> NoPatM [Match]
noPatArm ms = concat <$> mapM noPatM ms

noPatM :: Match -> NoPatM [Match]
noPatM (Match p e) =
  do (x,bs) <- noPat p
     e1     <- noPatE e
     return (Match x e1 : map MatchLet bs)
noPatM (MatchLet b) = (return . MatchLet) <$> noMatchB b

noMatchB :: Bind -> NoPatM Bind
noMatchB b =
  do (ps,e) <- noPatFun (bParams b) (bDef b)
     return b { bParams = ps, bDef = e }

noMatchD :: Decl -> NoPatM [Decl]
noMatchD decl =
  case decl of
    DSignature {}   -> return [decl]
    DPragma {}      -> return [decl]

    DBind b         -> do b1 <- noMatchB b
                          return [DBind b1]

    DPatBind p e    -> do (p',bs) <- noPat p
                          let (x,ts) = splitSimpleP p'
                          e1 <- noPatE e
                          let e2 = foldl ETyped e1 ts
                          return $ DBind Bind { bName = x
                                              , bParams = []
                                              , bDef = e2
                                              , bSignature = Nothing
                                              , bPragmas = []
                                              , bMono = False
                                              } : map DBind bs
    DType {}        -> return [decl]

    DLocated d r1   -> do bs <- inRange r1 $ noMatchD d
                          return $ map (`DLocated` r1) bs

noPatDs :: [Decl] -> NoPatM [Decl]
noPatDs ds =
  do ds1 <- concat <$> mapM noMatchD ds
     let pragmaMap = Map.fromListWith (++) $ concatMap toPragma ds1
         sigMap    = Map.fromListWith (++) $ concatMap toSig ds1
     (ds2, (pMap,sMap)) <- runStateT (pragmaMap, sigMap) $ annotDs ds1

     forM_ (Map.toList pMap) $ \(n,ps) ->
       forM_ ps $ \p -> recordError $ PragmaNoBind (p { thing = n }) (thing p)

     forM_ (Map.toList sMap) $ \(n,ss) ->
       do _ <- checkSigs n ss
          forM_ ss $ \s -> recordError $ SignatureNoBind (s { thing = n })
                                                         (thing s)

     return ds2

noPatTopDs :: [TopLevel Decl] -> NoPatM [TopLevel Decl]
noPatTopDs tds =
  do noPatGroups <- mapM (noMatchD . tlValue) tds

     let allDecls  = concat noPatGroups
         pragmaMap = Map.fromListWith (++) $ concatMap toPragma allDecls
         sigMap    = Map.fromListWith (++) $ concatMap toSig    allDecls

     let exportGroups = zipWith (\ td ds -> td { tlValue = ds }) tds noPatGroups
     (tds', (pMap,sMap)) <- runStateT (pragmaMap,sigMap) (annotTopDs exportGroups)

     forM_ (Map.toList pMap) $ \(n,ps) ->
       forM_ ps $ \p -> recordError $ PragmaNoBind (p { thing = n }) (thing p)

     forM_ (Map.toList sMap) $ \(n,ss) ->
       do _ <- checkSigs n ss
          forM_ ss $ \s -> recordError $ SignatureNoBind (s { thing = n })
                                                         (thing s)

     return tds'


noPatProg :: Program -> NoPatM Program
noPatProg (Program topDs) =
  do let (ds, others) = partitionEithers (map isDecl topDs)
     ds1 <- noPatTopDs ds
     return $ Program $ others ++ map Decl ds1

  where
  isDecl (Decl d) = Left d
  isDecl d        = Right d

noPatModule :: Module -> NoPatM Module
noPatModule m =
  do let (ds, others) = partitionEithers (map isDecl (mDecls m))
     ds1 <- noPatTopDs ds
     return m { mDecls = others ++ map Decl ds1 }

  where
  isDecl (Decl d) = Left d
  isDecl d        = Right d


--------------------------------------------------------------------------------

type AnnotMap = ( Map.Map QName [Located Pragma]
                , Map.Map QName [Located Schema]
                )

-- | Add annotations to exported declaration groups.
--
-- XXX: This isn't quite right: if a signature and binding have different
-- export specifications, this will favor the specification of the binding.
-- This is most likely the intended behavior, so it's probably fine, but it does
-- smell a bit.
annotTopDs :: [TopLevel [Decl]] -> StateT AnnotMap NoPatM [TopLevel Decl]
annotTopDs tds =
  case tds of

    (ds:dss) ->
      do ds'  <- annotDs (tlValue ds)
         rest <- annotTopDs dss
         if null ds'
            then return rest
            else return ([ ds { tlValue = d } | d <- ds' ] ++ rest)

    [] -> return []


-- | Add annotations, keeping track of which annotation are not yet used up.
annotDs :: [Decl] -> StateT AnnotMap NoPatM [Decl]
annotDs (d : ds) =
  do ignore <- runExceptionT (annotD d)
     case ignore of
       Left ()   -> annotDs ds
       Right d1  -> (d1 :) <$> annotDs ds
annotDs [] = return []

-- | Add annotations, keeping track of which annotation are not yet used up.
-- The exception indicates which declarations are no longer needed.
annotD :: Decl -> ExceptionT () (StateT AnnotMap NoPatM) Decl
annotD decl =
  case decl of
    DBind b       -> DBind <$> lift (annotB b)
    DSignature {} -> raise ()
    DPragma {}    -> raise ()
    DPatBind {}   -> raise ()
    DType {}      -> return decl
    DLocated d r  -> (`DLocated` r) <$> annotD d

-- | Add pragma/signature annotations to a binding.
annotB :: Bind -> StateT AnnotMap NoPatM Bind
annotB Bind { .. } =
  do (ps,ss) <- get
     let name = thing bName
     case ( Map.updateLookupWithKey (\_ _ -> Nothing) name ps
          , Map.updateLookupWithKey (\_ _ -> Nothing) name ss
          ) of
           ( (thisPs, pragmas1) , (thisSigs, sigs1)) ->
                do s <- lift $ checkSigs name (jn thisSigs)
                   set (pragmas1,sigs1)
                   return Bind { bSignature = s
                               , bPragmas = map thing (jn thisPs) ++ bPragmas
                               , ..
                               }
  where jn x = concat (maybeToList x)

-- | Check for multiple signatures.
checkSigs :: QName -> [Located Schema] -> NoPatM (Maybe Schema)
checkSigs _ []             = return Nothing
checkSigs _ [s]            = return (Just (thing s))
checkSigs f xs@(s : _ : _) = do recordError $ MultipleSignatures f xs
                                return (Just (thing s))


-- | Does this declaration provide some signatures?
toSig :: Decl -> [(QName, [Located Schema])]
toSig (DLocated d _)      = toSig d
toSig (DSignature xs s)   = [ (thing x,[Located (srcRange x) s]) | x <- xs ]
toSig _                   = []

-- | Does this declaration provide some signatures?
toPragma :: Decl -> [(QName, [Located Pragma])]
toPragma (DLocated d _)   = toPragma d
toPragma (DPragma xs s)   = [ (thing x,[Located (srcRange x) s]) | x <- xs ]
toPragma _                = []




--------------------------------------------------------------------------------
newtype NoPatM a = M { unM :: ReaderT Range (StateT RW Id) a }

data RW     = RW { names :: !Int, errors :: [Error] }

data Error  = MultipleSignatures QName [Located Schema]
            | SignatureNoBind (Located QName) Schema
            | PragmaNoBind (Located QName) Pragma
              deriving (Show)

instance Functor NoPatM where fmap = liftM
instance Applicative NoPatM where pure = return; (<*>) = ap
instance Monad NoPatM where
  return x  = M (return x)
  fail x    = M (fail x)
  M x >>= k = M (x >>= unM . k)


-- | Pick a new name, to be used when desugaring patterns.
newName :: NoPatM Name
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
        $$ nest 2 (vcat (map pp ss))

      SignatureNoBind x s ->
        text "At" <+> pp (srcRange x) <> colon <+>
        text "Type signature without a matching binding:"
         $$ nest 2 (pp s)

      PragmaNoBind x s ->
        text "At" <+> pp (srcRange x) <> colon <+>
        text "Pragma without a matching binding:"
         $$ nest 2 (pp s)




-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module defines the scoping rules for value- and type-level
-- names in Cryptol.

module Cryptol.Parser.Names where

import Cryptol.Parser.AST

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Foldable (fold)


modExports :: Module -> ExportSpec
modExports m = fold (concat [ exportedNames d | d <- mDecls m ])
  where
  names by td = [ td { tlValue = thing n } | n <- fst (by (tlValue td)) ]

  exportedNames (Decl td) = map exportBind  (names  namesD td)
                         ++ map exportType (names tnamesD td)
  exportedNames (TDNewtype nt) = map exportType (names tnamesNT nt)
  exportedNames (Include {})  = []

-- | The names defined by a newtype.
tnamesNT :: Newtype -> ([Located QName], ())
tnamesNT x = ([ nName x ], ())

-- | The names defined and used by a group of mutually recursive declarations.
namesDs :: [Decl] -> ([Located QName], Set QName)
namesDs ds = (defs, boundNames defs (Set.unions frees))
  where
  defs          = concat defss
  (defss,frees) = unzip (map namesD ds)

-- | The names defined and used by a single declarations.
namesD :: Decl -> ([Located QName], Set QName)
namesD decl =
  case decl of
    DBind b       -> namesB b
    DPatBind p e  -> (namesP p, namesE e)
    DSignature {} -> ([],Set.empty)
    DPragma {}    -> ([],Set.empty)
    DType {}      -> ([],Set.empty)
    DLocated d _  -> namesD d

-- | The names defined and used by a single declarations in such a way
-- that they cannot be duplicated in a file. For example, it is fine
-- to use @x@ on the RHS of two bindings, but not on the LHS of two
-- type signatures.
allNamesD :: Decl -> [Located QName]
allNamesD decl =
  case decl of
    DBind b         -> fst (namesB b)
    DPatBind p _    -> namesP p
    DSignature ns _ -> ns
    DPragma ns _    -> ns
    DType ts        -> [tsName ts]
    DLocated d _    -> allNamesD d

tsName :: TySyn -> Located QName
tsName (TySyn lqn _ _) = lqn

-- | The names defined and used by a single binding.
namesB :: Bind -> ([Located QName], Set QName)
namesB b = ([bName b], boundNames (namesPs (bParams b)) (namesE (bDef b)))


-- | The names used by an expression.
namesE :: Expr -> Set QName
namesE expr =
  case expr of
    EVar x        -> Set.singleton x
    ECon _        -> Set.empty
    ELit _        -> Set.empty
    ETuple es     -> Set.unions (map namesE es)
    ERecord fs    -> Set.unions (map (namesE . value) fs)
    ESel e _      -> namesE e
    EList es      -> Set.unions (map namesE es)
    EFromTo _ _ _ -> Set.empty
    EInfFrom e e' -> Set.union (namesE e) (maybe Set.empty namesE e')
    EComp e arms  -> let (dss,uss) = unzip (map namesArm arms)
                     in Set.union (boundNames (concat dss) (namesE e))
                                  (Set.unions uss)
    EApp e1 e2    -> Set.union (namesE e1) (namesE e2)
    EAppT e _     -> namesE e
    EIf e1 e2 e3  -> Set.union (namesE e1) (Set.union (namesE e2) (namesE e3))
    EWhere  e ds  -> let (bs,xs) = namesDs ds
                     in Set.union (boundNames bs (namesE e)) xs
    ETyped e _    -> namesE e
    ETypeVal _    -> Set.empty
    EFun ps e     -> boundNames (namesPs ps) (namesE e)
    ELocated e _  -> namesE e

-- | The names defined by a group of patterns.
namesPs :: [Pattern] -> [Located QName]
namesPs = concatMap namesP

-- | The names defined by a pattern.  These will always be unqualified names.
namesP :: Pattern -> [Located QName]
namesP pat =
  case pat of
    PVar x        -> [fmap mkUnqual x]
    PWild         -> []
    PTuple ps     -> namesPs ps
    PRecord fs    -> namesPs (map value fs)
    PList ps      -> namesPs ps
    PTyped p _    -> namesP p
    PSplit p1 p2  -> namesPs [p1,p2]
    PLocated p _  -> namesP p

-- | The names defined and used by a match.
namesM :: Match -> ([Located QName], Set QName)
namesM (Match p e)  = (namesP p, namesE e)
namesM (MatchLet b) = namesB b

-- | The names defined and used by an arm of alist comprehension.
namesArm :: [Match] -> ([Located QName], Set QName)
namesArm = foldr combine ([],Set.empty) . map namesM
  where combine (ds1,fs1) (ds2,fs2) =
          ( filter ((`notElem` map thing ds2) . thing) ds1 ++ ds2
          , Set.union fs1 (boundNames ds1 fs2)
          )

-- | Remove some defined variables from a set of free variables.
boundNames :: [Located QName] -> Set QName -> Set QName
boundNames bs xs = Set.difference xs (Set.fromList (map thing bs))


-- | Given the set of type variables that are in scope,
-- compute the type synonyms used by a type.
namesT :: Set QName -> Type -> Set QName
namesT vs = go
  where
  go ty =
    case ty of
      TWild         -> Set.empty
      TFun t1 t2    -> Set.union (go t1) (go t2)
      TSeq t1 t2    -> Set.union (go t1) (go t2)
      TBit          -> Set.empty
      TNum _        -> Set.empty
      TChar _       -> Set.empty
      TInf          -> Set.empty
      TApp _ ts     -> Set.unions (map go ts)
      TTuple ts     -> Set.unions (map go ts)
      TRecord fs    -> Set.unions (map (go . value) fs)
      TLocated t _  -> go t
      TUser x [] | x `Set.member` vs
                    -> Set.empty
      TUser x ts    -> Set.insert x (Set.unions (map go ts))


-- | The type names defined and used by a group of mutually recursive declarations.
tnamesDs :: [Decl] -> ([Located QName], Set QName)
tnamesDs ds = (defs, boundNames defs (Set.unions frees))
  where
  defs          = concat defss
  (defss,frees) = unzip (map tnamesD ds)

-- | The type names defined and used by a single declaration.
tnamesD :: Decl -> ([Located QName], Set QName)
tnamesD decl =
  case decl of
    DSignature _ s       -> ([], tnamesS s)
    DPragma {}           -> ([], Set.empty)
    DBind b              -> ([], tnamesB b)
    DPatBind _ e         -> ([], tnamesE e)
    DLocated d _         -> tnamesD d
    DType (TySyn n ps t) -> ([n], Set.difference (tnamesT t) (Set.fromList (map tpQName ps)))

-- | The type names used by a single binding.
tnamesB :: Bind -> Set QName
tnamesB b = Set.unions [setS, setP, setE]
  where
    setS = maybe Set.empty tnamesS (bSignature b)
    setP = Set.unions (map tnamesP (bParams b))
    setE = tnamesE (bDef b)

-- | The type names used by an expression.
tnamesE :: Expr -> Set QName
tnamesE expr =
  case expr of
    EVar _        -> Set.empty
    ECon _        -> Set.empty
    ELit _        -> Set.empty
    ETuple es     -> Set.unions (map tnamesE es)
    ERecord fs    -> Set.unions (map (tnamesE . value) fs)
    ESel e _      -> tnamesE e
    EList es      -> Set.unions (map tnamesE es)
    EFromTo a b c -> Set.union (tnamesT a)
                     (Set.union (maybe Set.empty tnamesT b) (maybe Set.empty tnamesT c))
    EInfFrom e e' -> Set.union (tnamesE e) (maybe Set.empty tnamesE e')
    EComp e mss   -> Set.union (tnamesE e) (Set.unions (map tnamesM (concat mss)))
    EApp e1 e2    -> Set.union (tnamesE e1) (tnamesE e2)
    EAppT e fs    -> Set.union (tnamesE e) (Set.unions (map tnamesTI fs))
    EIf e1 e2 e3  -> Set.union (tnamesE e1) (Set.union (tnamesE e2) (tnamesE e3))
    EWhere  e ds  -> let (bs,xs) = tnamesDs ds
                     in Set.union (boundNames bs (tnamesE e)) xs
    ETyped e t    -> Set.union (tnamesE e) (tnamesT t)
    ETypeVal t    -> tnamesT t
    EFun ps e     -> Set.union (Set.unions (map tnamesP ps)) (tnamesE e)
    ELocated e _  -> tnamesE e

tnamesTI :: TypeInst -> Set QName
tnamesTI (NamedInst f)  = tnamesT (value f)
tnamesTI (PosInst t)    = tnamesT t

-- | The type names used by a pattern.
tnamesP :: Pattern -> Set QName
tnamesP pat =
  case pat of
    PVar _        -> Set.empty
    PWild         -> Set.empty
    PTuple ps     -> Set.unions (map tnamesP ps)
    PRecord fs    -> Set.unions (map (tnamesP . value) fs)
    PList ps      -> Set.unions (map tnamesP ps)
    PTyped p t    -> Set.union (tnamesP p) (tnamesT t)
    PSplit p1 p2  -> Set.union (tnamesP p1) (tnamesP p2)
    PLocated p _  -> tnamesP p

-- | The type names used by a match.
tnamesM :: Match -> Set QName
tnamesM (Match p e)  = Set.union (tnamesP p) (tnamesE e)
tnamesM (MatchLet b) = tnamesB b

-- | The type names used by a type schema.
tnamesS :: Schema -> Set QName
tnamesS (Forall params props ty _) =
    Set.difference (Set.union (Set.unions (map tnamesC props)) (tnamesT ty))
        (Set.fromList (map tpQName params))

-- | The type names used by a prop.
tnamesC :: Prop -> Set QName
tnamesC prop =
  case prop of
    CFin t       -> tnamesT t
    CEqual t1 t2 -> Set.union (tnamesT t1) (tnamesT t2)
    CGeq t1 t2   -> Set.union (tnamesT t1) (tnamesT t2)
    CArith t     -> tnamesT t
    CCmp t       -> tnamesT t
    CLocated p _ -> tnamesC p

-- | Compute the type synonyms/type variables used by a type.
tnamesT :: Type -> Set QName
tnamesT ty =
  case ty of
    TWild         -> Set.empty
    TFun t1 t2    -> Set.union (tnamesT t1) (tnamesT t2)
    TSeq t1 t2    -> Set.union (tnamesT t1) (tnamesT t2)
    TBit          -> Set.empty
    TNum _        -> Set.empty
    TChar __      -> Set.empty
    TInf          -> Set.empty
    TApp _ ts     -> Set.unions (map tnamesT ts)
    TTuple ts     -> Set.unions (map tnamesT ts)
    TRecord fs    -> Set.unions (map (tnamesT . value) fs)
    TLocated t _  -> tnamesT t
    TUser x ts    -> Set.insert x (Set.unions (map tnamesT ts))

-- |
-- Module      :  Cryptol.Parser.Names
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module defines the scoping rules for value- and type-level
-- names in Cryptol.

{-# LANGUAGE Safe #-}

module Cryptol.Parser.Names
  ( tnamesNT
  , tnamesT
  , tnamesC

  , namesD
  , tnamesD
  , namesB
  , namesP
  , namesNT

  , boundNames
  , boundNamesSet
  ) where

import Cryptol.Parser.AST
import Cryptol.Utils.RecordMap

import           Data.Set (Set)
import qualified Data.Set as Set

-- | The names defined by a newtype.
tnamesNT :: Newtype name -> ([Located name], ())
tnamesNT x = ([ nName x ], ())

namesNT :: Newtype name -> ([Located name], ())
namesNT x = ([ (nName x) { thing = nConName x } ], ())

-- | The names defined and used by a group of mutually recursive declarations.
namesDs :: Ord name => [Decl name] -> ([Located name], Set name)
namesDs ds = (defs, boundLNames defs (Set.unions frees))
  where
  defs          = concat defss
  (defss,frees) = unzip (map namesD ds)

-- | The names defined and used by a single declarations.
namesD :: Ord name => Decl name -> ([Located name], Set name)
namesD decl =
  case decl of
    DBind b       -> namesB b
    DRec bs       -> let (xs,ys) = unzip (map namesB bs)
                     in (concat xs, Set.unions ys)  -- remove binders?
    DPatBind p e  -> (namesP p, namesE e)
    DSignature {} -> ([],Set.empty)
    DFixity{}     -> ([],Set.empty)
    DPragma {}    -> ([],Set.empty)
    DType {}      -> ([],Set.empty)
    DProp {}      -> ([],Set.empty)
    DLocated d _  -> namesD d

-- | The names defined and used by a single binding.
namesB :: Ord name => Bind name -> ([Located name], Set name)
namesB b =
  ([bName b], boundLNames (namesPs (bParams b)) (namesDef (thing (bDef b))))


namesDef :: Ord name => BindDef name -> Set name
namesDef DPrim     = Set.empty
namesDef DForeign  = Set.empty
namesDef (DExpr e) = namesE e
namesDef (DPropGuards guards) = Set.unions (map (namesE . pgcExpr) guards)


-- | The names used by an expression.
namesE :: Ord name => Expr name -> Set name
namesE expr =
  case expr of
    EVar x        -> Set.singleton x
    ELit _        -> Set.empty
    EGenerate e   -> namesE e
    ETuple es     -> Set.unions (map namesE es)
    ERecord fs    -> Set.unions (map (namesE . snd) (recordElements fs))
    ESel e _      -> namesE e
    EUpd mb fs    -> let e = maybe Set.empty namesE mb
                     in Set.unions (e : map namesUF fs)
    EList es      -> Set.unions (map namesE es)
    EFromTo{}     -> Set.empty
    EFromToBy{}   -> Set.empty
    EFromToDownBy{} -> Set.empty
    EFromToLessThan{} -> Set.empty
    EInfFrom e e' -> Set.union (namesE e) (maybe Set.empty namesE e')
    EComp e arms  -> let (dss,uss) = unzip (map namesArm arms)
                     in Set.union (boundLNames (concat dss) (namesE e))
                                  (Set.unions uss)
    EApp e1 e2    -> Set.union (namesE e1) (namesE e2)
    EAppT e _     -> namesE e
    EIf e1 e2 e3  -> Set.union (namesE e1) (Set.union (namesE e2) (namesE e3))
    EWhere  e ds  -> let (bs,xs) = namesDs ds
                     in Set.union (boundLNames bs (namesE e)) xs
    ETyped e _    -> namesE e
    ETypeVal _    -> Set.empty
    EFun _ ps e   -> boundLNames (namesPs ps) (namesE e)
    ELocated e _  -> namesE e

    ESplit e      -> namesE e
    EParens e     -> namesE e
    EInfix a o _ b-> Set.insert (thing o) (Set.union (namesE a) (namesE b))
    EPrefix _ e   -> namesE e

namesUF :: Ord name => UpdField name -> Set name
namesUF (UpdField _ _ e) = namesE e

-- | The names defined by a group of patterns.
namesPs :: [Pattern name] -> [Located name]
namesPs = concatMap namesP

-- | The names defined by a pattern.  These will always be unqualified names.
namesP :: Pattern name -> [Located name]
namesP pat =
  case pat of
    PVar x        -> [x]
    PWild         -> []
    PTuple ps     -> namesPs ps
    PRecord fs    -> namesPs (map snd (recordElements fs))
    PList ps      -> namesPs ps
    PTyped p _    -> namesP p
    PSplit p1 p2  -> namesPs [p1,p2]
    PLocated p _  -> namesP p

-- | The names defined and used by a match.
namesM :: Ord name => Match name -> ([Located name], Set name)
namesM (Match p e)  = (namesP p, namesE e)
namesM (MatchLet b) = namesB b

-- | The names defined and used by an arm of alist comprehension.
namesArm :: Ord name => [Match name] -> ([Located name], Set name)
namesArm = foldr combine ([],Set.empty) . map namesM
  where combine (ds1,fs1) (ds2,fs2) =
          ( filter ((`notElem` map thing ds2) . thing) ds1 ++ ds2
          , Set.union fs1 (boundLNames ds1 fs2)
          )

-- | Remove some defined variables from a set of free variables.
boundLNames :: Ord name => [Located name] -> Set name -> Set name
boundLNames = boundNames . map thing

-- | Remove some defined variables from a set of free variables.
boundNames :: Ord name => [name] -> Set name -> Set name
boundNames = boundNamesSet . Set.fromList

-- | Remove some defined variables from a set of free variables.
boundNamesSet :: Ord name => Set name -> Set name -> Set name
boundNamesSet bs xs = Set.difference xs bs


-- | The type names defined and used by a group of mutually recursive declarations.
tnamesDs :: Ord name => [Decl name] -> ([Located name], Set name)
tnamesDs ds = (defs, boundLNames defs (Set.unions frees))
  where
  defs          = concat defss
  (defss,frees) = unzip (map tnamesD ds)

-- | The type names defined and used by a single declaration.
tnamesD :: Ord name => Decl name -> ([Located name], Set name)
tnamesD decl =
  case decl of
    DSignature _ s       -> ([], tnamesS s)
    DFixity {}           -> ([], Set.empty)
    DPragma {}           -> ([], Set.empty)
    DBind b              -> ([], tnamesB b)
    DRec bs              -> ([], Set.unions (map tnamesB bs))
    DPatBind _ e         -> ([], tnamesE e)
    DLocated d _         -> tnamesD d
    DType (TySyn n _ ps t)
                         -> ([n], Set.difference (tnamesT t)
                                  (Set.fromList (map tpName ps)))
    DProp (PropSyn n _ ps cs)
                         -> ([n], Set.difference (Set.unions (map tnamesC cs))
                                  (Set.fromList (map tpName ps)))

-- | The type names used by a single binding.
tnamesB :: Ord name => Bind name -> Set name
tnamesB b = Set.unions [setS, setP, setE]
  where
    setS = maybe Set.empty tnamesS (bSignature b)
    setP = Set.unions (map tnamesP (bParams b))
    setE = tnamesDef (thing (bDef b))

tnamesDef :: Ord name => BindDef name -> Set name
tnamesDef DPrim     = Set.empty
tnamesDef DForeign  = Set.empty
tnamesDef (DExpr e) = tnamesE e
tnamesDef (DPropGuards guards) = Set.unions (map tnamesPropGuardCase guards)

tnamesPropGuardCase :: Ord name => PropGuardCase name -> Set name
tnamesPropGuardCase c =
  Set.unions (tnamesE (pgcExpr c) : map (tnamesC . thing) (pgcProps c))

-- | The type names used by an expression.
tnamesE :: Ord name => Expr name -> Set name
tnamesE expr =
  case expr of
    EVar _          -> Set.empty
    ELit _          -> Set.empty
    EGenerate e     -> tnamesE e
    ETuple es       -> Set.unions (map tnamesE es)
    ERecord fs      -> Set.unions (map (tnamesE . snd) (recordElements fs))
    ESel e _        -> tnamesE e
    EUpd mb fs      -> let e = maybe Set.empty tnamesE mb
                       in Set.unions (e : map tnamesUF fs)
    EList es        -> Set.unions (map tnamesE es)
    EFromTo a b c t -> tnamesT a
                       `Set.union` maybe Set.empty tnamesT b
                       `Set.union` tnamesT c
                       `Set.union` maybe Set.empty tnamesT t
    EFromToBy _ a b c t -> Set.unions [ tnamesT a, tnamesT b, tnamesT c, maybe Set.empty tnamesT t ]
    EFromToDownBy _ a b c t -> Set.unions [ tnamesT a, tnamesT b, tnamesT c, maybe Set.empty tnamesT t ]
    EFromToLessThan a b t -> tnamesT a `Set.union` tnamesT b
                                       `Set.union` maybe Set.empty tnamesT t
    EInfFrom e e'   -> Set.union (tnamesE e) (maybe Set.empty tnamesE e')
    EComp e mss     -> Set.union (tnamesE e) (Set.unions (map tnamesM (concat mss)))
    EApp e1 e2      -> Set.union (tnamesE e1) (tnamesE e2)
    EAppT e fs      -> Set.union (tnamesE e) (Set.unions (map tnamesTI fs))
    EIf e1 e2 e3    -> Set.union (tnamesE e1) (Set.union (tnamesE e2) (tnamesE e3))
    EWhere  e ds    -> let (bs,xs) = tnamesDs ds
                       in Set.union (boundLNames bs (tnamesE e)) xs
    ETyped e t      -> Set.union (tnamesE e) (tnamesT t)
    ETypeVal t      -> tnamesT t
    EFun _ ps e     -> Set.union (Set.unions (map tnamesP ps)) (tnamesE e)
    ELocated e _    -> tnamesE e

    ESplit e        -> tnamesE e
    EParens e       -> tnamesE e
    EInfix a _ _ b  -> Set.union (tnamesE a) (tnamesE b)
    EPrefix _ e     -> tnamesE e

tnamesUF :: Ord name => UpdField name -> Set name
tnamesUF (UpdField _ _ e) = tnamesE e

tnamesTI :: Ord name => TypeInst name -> Set name
tnamesTI (NamedInst f)  = tnamesT (value f)
tnamesTI (PosInst t)    = tnamesT t

-- | The type names used by a pattern.
tnamesP :: Ord name => Pattern name -> Set name
tnamesP pat =
  case pat of
    PVar _        -> Set.empty
    PWild         -> Set.empty
    PTuple ps     -> Set.unions (map tnamesP ps)
    PRecord fs    -> Set.unions (map (tnamesP . snd) (recordElements fs))
    PList ps      -> Set.unions (map tnamesP ps)
    PTyped p t    -> Set.union (tnamesP p) (tnamesT t)
    PSplit p1 p2  -> Set.union (tnamesP p1) (tnamesP p2)
    PLocated p _  -> tnamesP p

-- | The type names used by a match.
tnamesM :: Ord name => Match name -> Set name
tnamesM (Match p e)  = Set.union (tnamesP p) (tnamesE e)
tnamesM (MatchLet b) = tnamesB b

-- | The type names used by a type schema.
tnamesS :: Ord name => Schema name -> Set name
tnamesS (Forall params props ty _) =
    Set.difference (Set.union (Set.unions (map tnamesC props)) (tnamesT ty))
        (Set.fromList (map tpName params))

-- | The type names used by a prop.
tnamesC :: Ord name => Prop name -> Set name
tnamesC prop =
  case prop of
    CType t        -> tnamesT t

-- | Compute the type synonyms/type variables used by a type.
tnamesT :: Ord name => Type name -> Set name
tnamesT ty =
  case ty of
    TWild         -> Set.empty
    TFun t1 t2    -> Set.union (tnamesT t1) (tnamesT t2)
    TSeq t1 t2    -> Set.union (tnamesT t1) (tnamesT t2)
    TBit          -> Set.empty
    TNum _        -> Set.empty
    TChar __      -> Set.empty
    TTuple ts     -> Set.unions (map tnamesT ts)
    TRecord fs    -> Set.unions (map (tnamesT . snd) (recordElements fs))
    TTyApp fs     -> Set.unions (map (tnamesT . value) fs)
    TLocated t _  -> tnamesT t
    TUser x ts    -> Set.insert x (Set.unions (map tnamesT ts))
    TParens t _   -> tnamesT t
    TInfix a x _ c-> Set.insert (thing x)
                                (Set.union (tnamesT a) (tnamesT c))

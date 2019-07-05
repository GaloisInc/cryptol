-- |
-- Module      :  Cryptol.TypeCheck.Depends
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE FlexibleInstances #-}
module Cryptol.TypeCheck.Depends where

import           Cryptol.ModuleSystem.Name (Name)
import qualified Cryptol.Parser.AST as P
import           Cryptol.Parser.Position(Range, Located(..), thing)
import           Cryptol.Parser.Names (namesB, tnamesT, tnamesC,
                                      boundNamesSet, boundNames)
import           Cryptol.TypeCheck.Monad( InferM, recordError, getTVars )
import           Cryptol.TypeCheck.Error(Error(..))
import           Cryptol.Utils.Panic(panic)

import           Data.List(sortBy, groupBy)
import           Data.Function(on)
import           Data.Maybe(mapMaybe)
import           Data.Graph.SCC(stronglyConnComp)
import           Data.Graph (SCC(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

data TyDecl =
    TS (P.TySyn Name) (Maybe String)          -- ^ Type synonym
  | NT (P.Newtype Name) (Maybe String)        -- ^ Newtype
  | AT (P.ParameterType Name) (Maybe String)  -- ^ Parameter type
  | PS (P.PropSyn Name) (Maybe String)        -- ^ Property synonym
  | PT (P.PrimType Name) (Maybe String)       -- ^ A primitive/abstract typee
    deriving Show

setDocString :: Maybe String -> TyDecl -> TyDecl
setDocString x d =
  case d of
    TS a _ -> TS a x
    PS a _ -> PS a x
    NT a _ -> NT a x
    AT a _ -> AT a x
    PT a _ -> PT a x

-- | Check for duplicate and recursive type synonyms.
-- Returns the type-synonyms in dependency order.
orderTyDecls :: [TyDecl] -> InferM [TyDecl]
orderTyDecls ts =
  do vs <- getTVars
     ds <- combine $ map (toMap vs) ts
     let ordered = mkScc [ (t,[x],deps)
                              | (x,(t,deps)) <- Map.toList (Map.map thing ds) ]
     concat `fmap` mapM check ordered

  where
  toMap vs ty@(PT p _) =
    let x       = P.primTName p
        (as,cs) = P.primTCts p
    in  ( thing x
        , x { thing = (ty, Set.toList $
                           boundNamesSet vs $
                           boundNames (map P.tpName as) $
                           Set.unions $
                           map tnamesC cs
                      )
             }
        )


  toMap _ ty@(AT a _) =
    let x = P.ptName a
    in ( thing x, x { thing = (ty, []) } )

  toMap vs ty@(NT (P.Newtype x as fs) _) =
    ( thing x
    , x { thing = (ty, Set.toList $
                       boundNamesSet vs $
                       boundNames (map P.tpName as) $
                       Set.unions $
                       map (tnamesT . P.value) fs
                  )
        }
    )

  toMap vs ty@(TS (P.TySyn x _ as t) _) =
        (thing x
        , x { thing = (ty, Set.toList $
                           boundNamesSet vs $
                           boundNames (map P.tpName as) $
                           tnamesT t
                      )
             }
        )

  toMap vs ty@(PS (P.PropSyn x _ as ps) _) =
        (thing x
        , x { thing = (ty, Set.toList $
                           boundNamesSet vs $
                           boundNames (map P.tpName as) $
                           Set.unions $
                           map tnamesC ps
                      )
             }
        )
  getN (TS x _) = thing (P.tsName x)
  getN (PS x _) = thing (P.psName x)
  getN (NT x _) = thing (P.nName x)
  getN (AT x _) = thing (P.ptName x)
  getN (PT x _) = thing (P.primTName x)

  check (AcyclicSCC x) = return [x]

  -- We don't support any recursion, for now.
  -- We could support recursion between newtypes, or newtypes and tysysn.
  check (CyclicSCC xs) =
    do recordError (RecursiveTypeDecls (map getN xs))
       return [] -- XXX: This is likely to cause fake errors for missing
                 -- type synonyms. We could avoid this by, for example, checking
                 -- for recursive synonym errors, when looking up tycons.



-- | Associate type signatures with bindings and order bindings by dependency.
orderBinds :: [P.Bind Name] -> [SCC (P.Bind Name)]
orderBinds bs = mkScc [ (b, map thing defs, Set.toList uses)
                      | b <- bs
                      , let (defs,uses) = namesB b
                      ]

class FromDecl d where
  toBind             :: d -> Maybe (P.Bind Name)
  toParamFun         :: d -> Maybe (P.ParameterFun Name)
  toParamConstraints :: d -> [P.Located (P.Prop Name)]
  toTyDecl           :: d -> Maybe TyDecl
  isTopDecl          :: d -> Bool

instance FromDecl (P.TopDecl Name) where
  toBind (P.Decl x)         = toBind (P.tlValue x)
  toBind _                  = Nothing

  toParamFun (P.DParameterFun d)  = Just d
  toParamFun _                    = Nothing

  toParamConstraints (P.DParameterConstraint xs) = xs
  toParamConstraints _                           = []

  toTyDecl (P.DPrimType p)      = Just (PT (P.tlValue p) (thing <$> P.tlDoc p))
  toTyDecl (P.DParameterType d) = Just (AT d (P.ptDoc d))
  toTyDecl (P.TDNewtype d)      = Just (NT (P.tlValue d) (thing <$> P.tlDoc d))
  toTyDecl (P.Decl x)           = setDocString (thing <$> P.tlDoc x)
                                  <$> toTyDecl (P.tlValue x)
  toTyDecl _                    = Nothing

  isTopDecl _               = True

instance FromDecl (P.Decl Name) where
  toBind (P.DLocated d _) = toBind d
  toBind (P.DBind b)      = return b
  toBind _                = Nothing

  toParamFun _ = Nothing
  toParamConstraints _ = []

  toTyDecl (P.DLocated d _) = toTyDecl d
  toTyDecl (P.DType x)      = Just (TS x Nothing)
  toTyDecl (P.DProp x)      = Just (PS x Nothing)
  toTyDecl _                = Nothing

  isTopDecl _               = False

{- | Given a list of declarations, annoted with (i) the names that they
define, and (ii) the names that they use, we compute a list of strongly
connected components of the declarations.  The SCCs are in dependency order. -}
mkScc :: [(a,[Name],[Name])] -> [SCC a]
mkScc ents = stronglyConnComp $ zipWith mkGr keys ents
  where
  keys                    = [ 0 :: Integer .. ]

  mkGr i (x,_,uses)       = (x,i,mapMaybe (`Map.lookup` nodeMap) uses)

  -- Maps names to node ids.
  nodeMap                 = Map.fromList $ concat $ zipWith mkNode keys ents
  mkNode i (_,defs,_)     = [ (d,i) | d <- defs ]

{- | Combine a bunch of definitions into a single map.  Here we check
that each name is defined only onces. -}
combineMaps :: [Map Name (Located a)] -> InferM (Map Name (Located a))
combineMaps ms = if null bad then return (Map.unions ms)
                             else panic "combineMaps" $ "Multiple definitions"
                                                      : map show bad
  where
  bad = do m <- ms
           duplicates [ a { thing = x } | (x,a) <- Map.toList m ]

{- | Combine a bunch of definitions into a single map.  Here we check
that each name is defined only onces. -}
combine :: [(Name, Located a)] -> InferM (Map Name (Located a))
combine m = if null bad then return (Map.fromList m)
                        else panic "combine" $ "Multiple definitions"
                                             : map show bad
  where
  bad = duplicates [ a { thing = x } | (x,a) <- m ]

-- | Identify multiple occurances of something.
duplicates :: Ord a => [Located a] -> [(a,[Range])]
duplicates = mapMaybe multiple
           . groupBy ((==) `on` thing)
           . sortBy (compare `on` thing)
  where
  multiple xs@(x : _ : _) = Just (thing x, map srcRange xs)
  multiple _              = Nothing



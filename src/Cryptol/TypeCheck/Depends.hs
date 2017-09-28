-- |
-- Module      :  $Header$
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
import           Cryptol.Parser.Names (namesB, namesT, namesC)
import           Cryptol.TypeCheck.Monad( InferM, recordError, getTVars
                                        , Error(..))

import           Data.List(sortBy, groupBy)
import           Data.Function(on)
import           Data.Maybe(mapMaybe)
import           Data.Graph.SCC(stronglyConnComp)
import           Data.Graph (SCC(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

data TyDecl = TS (P.TySyn Name) (Maybe String)
            | PS (P.PropSyn Name) (Maybe String)
            | NT (P.Newtype Name) (Maybe String)

setDocString :: Maybe String -> TyDecl -> TyDecl
setDocString x d =
  case d of
    TS a _ -> TS a x
    PS a _ -> PS a x
    NT a _ -> NT a x

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
  toMap vs ty@(NT (P.Newtype x as fs) _) =
    ( thing x
    , x { thing = (ty, Set.toList $
                       Set.difference
                         (Set.unions (map (namesT vs . P.value) fs))
                         (Set.fromList (map P.tpName as))
                  )
        }
    )

  toMap vs ty@(TS (P.TySyn x as t) _) =
        (thing x
        , x { thing = (ty, Set.toList $
                           Set.difference (namesT vs t)
                                          (Set.fromList (map P.tpName as)))
             }
        )

  toMap vs ty@(PS (P.PropSyn x as ps) _) =
        (thing x
        , x { thing = (ty, Set.toList $
                           Set.difference (Set.unions (map (namesC vs) ps))
                                          (Set.fromList (map P.tpName as)))
             }
        )
  getN (TS (P.TySyn x _ _) _)   = thing x
  getN (PS (P.PropSyn x _ _) _) = thing x
  getN (NT x _)                 = thing (P.nName x)

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
  toBind    :: d -> Maybe (P.Bind Name)
  toTyDecl  :: d -> Maybe TyDecl
  isTopDecl :: d -> Bool

instance FromDecl (P.TopDecl Name) where
  toBind (P.Decl x)         = toBind (P.tlValue x)
  toBind _                  = Nothing

  toTyDecl (P.TDNewtype d)  = Just (NT (P.tlValue d) (thing <$> P.tlDoc d))
  toTyDecl (P.Decl x)       = setDocString (thing <$> P.tlDoc x)
                                  <$> toTyDecl (P.tlValue x)
  toTyDecl _                = Nothing

  isTopDecl _               = True

instance FromDecl (P.Decl Name) where
  toBind (P.DLocated d _) = toBind d
  toBind (P.DBind b)      = return b
  toBind _                = Nothing

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
combineMaps ms  =
   do mapM_ recordError $
        do m <- ms
           (x,rs) <- duplicates [ a { thing = x } | (x,a) <- Map.toList m ]
           return (RepeatedDefinitions x rs)
      return (Map.unions ms)

{- | Combine a bunch of definitions into a single map.  Here we check
that each name is defined only onces. -}
combine :: [(Name, Located a)] -> InferM (Map Name (Located a))
combine m =
  do mapM_ recordError $
      do (x,rs) <- duplicates [ a { thing = x } | (x,a) <- m ]
         return (RepeatedDefinitions x rs)
     return (Map.fromList m)

-- | Identify multiple occurances of something.
duplicates :: Ord a => [Located a] -> [(a,[Range])]
duplicates = mapMaybe multiple
           . groupBy ((==) `on` thing)
           . sortBy (compare `on` thing)
  where
  multiple xs@(x : _ : _) = Just (thing x, map srcRange xs)
  multiple _              = Nothing



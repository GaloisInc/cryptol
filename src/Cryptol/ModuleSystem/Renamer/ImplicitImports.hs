{- |
We add implicit imports are for public nested modules.  This allows
using definitions from nested modules without having to explicitly import
them, for example:

module A where

  submodule B where
    x = 0x20

  y = x     // This works because of the implicit import of `B`

Restriction:
============

We only add impicit imports of modules that are syntactically visiable
in the source code.  Consider the following example:

module A where
  submodule M = F {X}   -- F,X are external modules (e.g., top-level)

We will add an implicit import for `M`, but *NO* implicit imports for
any modules imported vial `M` as those are not sytnactically visible
in the source (i.e., we have to know what `F` refers to).

This restriction allows us to add implicit imports before doing the
`Imports` pass.
-}

module Cryptol.ModuleSystem.Renamer.ImplicitImports
  ( addImplicitNestedImports
  ) where

import Data.List(partition)

import Cryptol.Parser.Position(Range)
import Cryptol.Utils.Ident(packModName)
import Cryptol.Parser.AST

{- | Add additional imports for modules nested withing this one -}
addImplicitNestedImports :: [TopDecl PName] -> [TopDecl PName]
addImplicitNestedImports = snd . addImplicitNestedImports'

{- | Returns:

  * declarations with additional imports and
  * the public module names of this module and its children.
-}
addImplicitNestedImports' ::
  [TopDecl PName] -> ([[Ident]], [TopDecl PName])
addImplicitNestedImports' decls =
  (concat exportedMods, concat newDecls ++ other)
  where
  (mods,other)            = partition isNestedMod decls
  (newDecls,exportedMods) = unzip (map processModule mods)


processModule :: TopDecl PName -> ([TopDecl PName], [[Ident]])
processModule ~dcl@(DModule m) =
  let NestedModule m1 = tlValue m
  in
  case mDef m1 of
    NormalModule ds ->
      let (childExs, ds1) = addImplicitNestedImports' ds
          mname           = getIdent (thing (mName m1))
          imps            = map (mname :) ([] : childExs) -- this & nested
          loc             = srcRange (mName m1)
      in ( DModule m { tlValue = NestedModule m1 { mDef = NormalModule ds1 } }
         : map (mkImp loc) imps
         , case tlExport m of
             Public  -> imps
             Private -> []
         )

    FunctorInstance {} -> ([dcl], [])
    InterfaceModule {} -> ([dcl], [])




isNestedMod :: TopDecl name -> Bool
isNestedMod d =
  case d of
    DModule tl -> case tlValue tl of
                    NestedModule m -> not (mIsFunctor m)
    _          -> False

-- | Make a name qualifier out of a list of identifiers.
isToQual :: [Ident] -> ModName
isToQual is = packModName (map identText is)

-- | Make a module name out of a list of identifier.
-- This is the name of the module we are implicitly importing.
isToName :: [Ident] -> PName
isToName is = case is of
                [i] -> mkUnqual i
                _   -> mkQual (isToQual (init is)) (last is)

-- | Make an implicit import declaration.
mkImp :: Range -> [Ident] -> TopDecl PName
mkImp loc xs =
  DImport
    Located
      { srcRange = loc
      , thing    = Import
                     { iModule = ImpNested (isToName xs)
                     , iAs     = Just (isToQual xs)
                     , iSpec   = Nothing
                     , iInst   = Nothing
                     , iDoc    = Nothing
                     }
      }




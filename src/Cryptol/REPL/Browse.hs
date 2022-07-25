{-# Language OverloadedStrings, BlockArguments #-}
module Cryptol.REPL.Browse (BrowseHow(..), browseModContext) where

import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe(mapMaybe)
import Data.List(sortBy)
import Data.Void (Void)
import qualified Prettyprinter as PP

import Cryptol.Parser.AST(Pragma(..))
import qualified Cryptol.TypeCheck.Type as T

import Cryptol.Utils.PP
import Cryptol.Utils.Ident(OrigName(..))
import Cryptol.ModuleSystem.Env(ModContext(..))
import Cryptol.ModuleSystem.NamingEnv(namingEnvNames)
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Interface

data BrowseHow = BrowseExported | BrowseInScope

browseModContext :: BrowseHow -> ModContext -> PP.Doc Void
browseModContext how mc =
  runDoc (env disp) (vcat sections)
  where
  sections = concat
    [ browseMParams (env disp) (mctxParams mc)
    , browseSignatures disp decls
    , browseMods disp decls
    , browseFunctors disp decls
    , browseTSyns disp decls
    , browsePrimTys disp decls
    , browseNewtypes disp decls
    , browseVars disp decls
    ]

  disp     = DispInfo { dispHow = how, env = mctxNameDisp mc }
  decls    = filterIfaceDecls (`Set.member` visNames) (mctxDecls mc)
  allNames = namingEnvNames (mctxNames mc)
  visNames = case how of
               BrowseInScope  -> allNames
               BrowseExported -> mctxExported mc

data DispInfo = DispInfo { dispHow :: BrowseHow, env :: NameDisp }

--------------------------------------------------------------------------------


browseMParams :: NameDisp -> T.FunctorParams -> [Doc]
browseMParams disp params
  | Map.null params = []
  | otherwise =
      ppSectionHeading "Module Parameters"
      $ [ "parameter" <+> pp (T.mpName p) <+> ":" <+>
          "interface" <+> pp (T.mpSignature p) $$
           indent 2 (vcat $
            map ppParamTy (sortByName disp (Map.toList (T.mpnTypes names))) ++
            map ppParamFu (sortByName disp (Map.toList (T.mpnFuns  names)))
           )
        | p <- Map.elems params
        , let names = T.mpParameters p
        ] ++
        ["   "]
  where
  ppParamTy p = nest 2 (sep ["type", pp (T.mtpName p) <+> ":", pp (T.mtpKind p)])
  ppParamFu p = nest 2 (sep [pp (T.mvpName p) <+> ":", pp (T.mvpType p)])
  -- XXX: should we print the constraints somewhere too?


browseMods :: DispInfo -> IfaceDecls -> [Doc]
browseMods disp decls =
  ppSection disp "Modules" ppM (ifModules decls)
  where
  ppM m = "submodule" <+> pp (ifsName m)
  -- XXX: can print a lot more information about the moduels, but
  -- might be better to do that with a separate command

browseFunctors :: DispInfo -> IfaceDecls -> [Doc]
browseFunctors disp decls =
  ppSection disp "Functors" ppM (ifFunctors decls)
  where
  ppM m = "submodule" <+> pp (ifModName m)




browseSignatures :: DispInfo -> IfaceDecls -> [Doc]
browseSignatures disp decls =
  ppSection disp "Interfaces" ppS (Map.mapWithKey (,) (ifSignatures decls))
  where
  ppS (x,s) = "interface submodule" <+> pp x


browseTSyns :: DispInfo -> IfaceDecls -> [Doc]
browseTSyns disp decls =
     ppSection disp "Type Synonyms" pp tss
  ++ ppSection disp "Constraint Synonyms" pp cts
  where
  (cts,tss)  = Map.partition isCtrait (ifTySyns decls)
  isCtrait t = T.kindResult (T.kindOf (T.tsDef t)) == T.KProp

browsePrimTys :: DispInfo -> IfaceDecls -> [Doc]
browsePrimTys disp decls =
  ppSection disp "Primitive Types" ppA (ifAbstractTypes decls)
  where
  ppA a = nest 2 (sep [pp (T.atName a) <+> ":", pp (T.atKind a)])

browseNewtypes :: DispInfo -> IfaceDecls -> [Doc]
browseNewtypes disp decls =
  ppSection disp "Newtypes" T.ppNewtypeShort (ifNewtypes decls)

browseVars :: DispInfo -> IfaceDecls -> [Doc]
browseVars disp decls =
     ppSection disp "Properties" ppVar props
  ++ ppSection disp "Symbols"    ppVar syms
  where
  isProp p     = PragmaProperty `elem` ifDeclPragmas p
  (props,syms) = Map.partition isProp (ifDecls decls)

  ppVar d      = nest 2 (sep [pp (ifDeclName d) <+> ":", pp (ifDeclSig d)])

--------------------------------------------------------------------------------

ppSection :: DispInfo -> String -> (a -> Doc) -> Map Name a -> [Doc]
ppSection disp heading ppThing mp =
  ppSectionHeading heading 
  case dispHow disp of
    BrowseExported | [(_,xs)] <- grouped -> ppThings xs
    _ -> concatMap ppMod grouped
  where
  grouped = groupDecls (env disp) mp

  ppThings xs = map ppThing xs ++ [" "]

  ppMod (nm,things) =
    [ "From" <+> pp nm
    , "-----" <.> text (map (const '-') (show (runDoc (env disp) (pp nm))))
    , "     "
    , indent 2 (vcat (ppThings things))
    ]

ppSectionHeading :: String -> [Doc] -> [Doc]
ppSectionHeading heading body
  | null body = []
  | otherwise = 
     [ text heading
     , text (map (const '=') heading)
     , "    "
     , indent 2 (vcat body)
     ]




-- | Organize by module where defined, then sort by name.
groupDecls :: NameDisp -> Map Name a -> [(ModPath,[a])]
groupDecls disp = Map.toList
                . fmap (sortByName disp)
                . Map.fromListWith (++)
                . mapMaybe toEntry
                . Map.toList
  where
  toEntry (n,a) =
    case nameInfo n of
      GlobalName _ og -> Just (ogModule og,[(n,a)])
      _               -> Nothing


sortByName :: NameDisp -> [(Name,a)] -> [a]
sortByName disp = map snd . sortBy cmpByDispName
  where
  cmpByDispName (x,_) (y,_) =  cmpNameDisplay disp x y




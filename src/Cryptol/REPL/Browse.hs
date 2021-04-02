{-# Language OverloadedStrings, BlockArguments #-}
module Cryptol.REPL.Browse (BrowseHow(..), browseModContext) where

import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe(mapMaybe)
import Data.List(sortBy)
import qualified Text.PrettyPrint as PP

import Cryptol.Parser.AST(Pragma(..))
import qualified Cryptol.TypeCheck.Type as T

import Cryptol.Utils.PP
import Cryptol.ModuleSystem.Env(ModContext(..))
import Cryptol.ModuleSystem.NamingEnv(namingEnvNames)
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Interface

data BrowseHow = BrowseExported | BrowseInScope

browseModContext :: BrowseHow -> ModContext -> PP.Doc
browseModContext how mc = runDoc (env disp) (vcat sections)
  where
  sections =
    [ browseMParams (env disp) (mctxParams mc)
    , browseMods disp decls
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


browseMParams :: NameDisp -> IfaceParams -> Doc
browseMParams disp params =
  ppSectionHeading "Module Parameters"
  $ addEmpty
  $ map ppParamTy (sortByName disp (Map.toList (ifParamTypes params))) ++
    map ppParamFu (sortByName disp (Map.toList (ifParamFuns  params)))
  where
  ppParamTy p = hang ("type" <+> pp (T.mtpName p) <+> ":") 2 (pp (T.mtpKind p))
  ppParamFu p = hang (pp (T.mvpName p) <+> ":") 2 (pp (T.mvpType p))
  -- XXX: should we print the constraints somewhere too?

  addEmpty xs = case xs of
                  [] -> []
                  _  -> xs ++ ["    "]


browseMods :: DispInfo -> IfaceDecls -> Doc
browseMods disp decls =
  ppSection disp "Modules" ppM (ifModules decls)
  where
  ppM m = "submodule" <+> pp (ifModName m)
  -- XXX: can print a lot more information about the moduels, but
  -- might be better to do that with a separate command




browseTSyns :: DispInfo -> IfaceDecls -> Doc
browseTSyns disp decls =
     ppSection disp "Type Synonyms" pp tss
  $$ ppSection disp "Constraint Synonyms" pp cts
  where
  (cts,tss)  = Map.partition isCtrait (ifTySyns decls)
  isCtrait t = T.kindResult (T.kindOf (T.tsDef t)) == T.KProp

browsePrimTys :: DispInfo -> IfaceDecls -> Doc
browsePrimTys disp decls =
  ppSection disp "Primitive Types" ppA (ifAbstractTypes decls)
  where
  ppA a = pp (T.atName a) <+> ":" <+> pp (T.atKind a)

browseNewtypes :: DispInfo -> IfaceDecls -> Doc
browseNewtypes disp decls =
  ppSection disp "Newtypes" T.ppNewtypeShort (ifNewtypes decls)

browseVars :: DispInfo -> IfaceDecls -> Doc
browseVars disp decls =
     ppSection disp "Properties" ppVar props
  $$ ppSection disp "Symbols"    ppVar syms
  where
  isProp p     = PragmaProperty `elem` ifDeclPragmas p
  (props,syms) = Map.partition isProp (ifDecls decls)

  ppVar d      = hang (pp (ifDeclName d) <+> char ':') 2 (pp (ifDeclSig d))


--------------------------------------------------------------------------------

ppSection :: DispInfo -> String -> (a -> Doc) -> Map Name a -> Doc
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
    , nest 2 (vcat (ppThings things))
    ]

ppSectionHeading :: String -> [Doc] -> Doc
ppSectionHeading heading body
  | null body = empty
  | otherwise = 
    vcat [ text heading
         , text (map (const '=') heading)
         , "    "
         , nest 2 (vcat body)
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
      Declared m _ -> Just (m,[(n,a)])
      _            -> Nothing


sortByName :: NameDisp -> [(Name,a)] -> [a]
sortByName disp = map snd . sortBy cmpByDispName
  where
  cmpByDispName (x,_) (y,_) =  cmpNameDisplay disp x y




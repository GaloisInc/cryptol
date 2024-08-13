{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
module Cryptol.REPL.Help (helpForNamed) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(fromMaybe, maybeToList)
import Data.List(intersperse)
import Data.Foldable (for_)
import Control.Monad(when,guard,unless,msum,mplus)

import Cryptol.Utils.PP
import Cryptol.Utils.Ident(OrigName(..),identIsNormal)
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Name as M
import qualified Cryptol.ModuleSystem.NamingEnv as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Interface as M
import qualified Cryptol.ModuleSystem.Renamer.Error as M (ModKind(..))
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.TypeCheck.PP(emptyNameMap,ppWithNames)

import Cryptol.REPL.Monad

helpForNamed :: P.PName -> REPL Bool
helpForNamed qname =
  do fe <- getFocusedEnv
     let params = M.mctxParams fe
         env    = M.mctxDecls  fe
         rnEnv  = M.mctxNames  fe
         disp   = M.mctxNameDisp fe

         vNames = M.lookupListNS M.NSValue       qname rnEnv
         cNames = M.lookupListNS M.NSConstructor qname rnEnv
         tNames = M.lookupListNS M.NSType        qname rnEnv
         mNames = M.lookupListNS M.NSModule      qname rnEnv

     let helps = map (showTypeHelp params env disp) tNames ++
                 map (showValHelp params env disp qname) vNames ++
                 map (showConHelp env disp qname) cNames ++
                 map (showModHelp env disp) mNames

         separ = rPutStrLn "            ---------"
     sequence_ (intersperse separ helps)

     let failure = null (vNames ++ cNames ++ tNames ++ mNames)
     when failure $
       rPrint $ "Undefined name:" <+> pp qname
    
     pure (not failure)


noInfo :: NameDisp -> M.Name -> REPL ()
noInfo nameEnv name =
  case M.nameInfo name of
    M.GlobalName _ og ->
      rPrint (runDoc nameEnv ("Name defined in module" <+> pp (ogModule og)))
    M.LocalName {} -> rPutStrLn "// No documentation is available."


-- | Show help for something in the module namespace.
showModHelp :: M.IfaceDecls -> NameDisp -> M.Name -> REPL ()
showModHelp env nameEnv name =
  fromMaybe (noInfo nameEnv name) $
    msum [ attempt M.ifModules showModuleHelp
         , attempt M.ifFunctors showFunctorHelp
         , attempt M.ifSignatures showSigHelp
         ]

  where
  attempt :: (M.IfaceDecls -> Map M.Name a) ->
             (M.IfaceDecls -> NameDisp -> M.Name -> a -> REPL ()) ->
             Maybe (REPL ())
  attempt inMap doShow =
    do th <- Map.lookup name (inMap env)
       pure (doShow env nameEnv name th)

showModuleHelp ::
  M.IfaceDecls -> NameDisp -> M.Name -> M.IfaceNames M.Name -> REPL ()
showModuleHelp env _nameEnv name info =
  showSummary M.AModule name (M.ifsDoc info) (ifaceSummary env info)

ifaceSummary :: M.IfaceDecls -> M.IfaceNames M.Name -> ModSummary
ifaceSummary env info =
    foldr addName emptySummary (Set.toList (M.ifsPublic info))
  where
  addName x ns = fromMaybe ns
               $ msum [ addT <$> msum [fromTS, fromNT ]
                      , addV <$> fromD
                      , addM <$> msum [ fromM, fromS, fromF ]
                      ]
    where 
    addT (k,d) = ns { msTypes = T.ModTParam { T.mtpName = x
                                            , T.mtpKind = k
                                            , T.mtpDoc  = d
                                            } : msTypes ns }

    addV (t,d,f) = ns { msVals = T.ModVParam { T.mvpName = x
                                             , T.mvpType = t
                                             , T.mvpDoc  = d
                                             , T.mvpFixity = f
                                             } : msVals ns }

    addM (k,d)= ns { msMods = (x, k, d) : msMods ns }


    fromTS = do def <- Map.lookup x (M.ifTySyns env)
                pure (T.kindOf def, T.tsDoc def)

    fromNT = do def <- Map.lookup x (M.ifNominalTypes env)
                pure (T.kindOf def, T.ntDoc def)

    fromD = do def <- Map.lookup x (M.ifDecls env)
               pure (M.ifDeclSig def, M.ifDeclDoc def, M.ifDeclFixity def)

    fromM = do def <- Map.lookup x (M.ifModules env)
               pure (M.AModule, M.ifsDoc def)

    fromF = do def <- Map.lookup x (M.ifFunctors env)
               pure (M.AFunctor, M.ifsDoc (M.ifNames def))

    fromS = do def <- Map.lookup x (M.ifSignatures env)
               pure (M.ASignature, maybeToList (T.mpnDoc def))



showFunctorHelp ::
  M.IfaceDecls -> NameDisp -> M.Name -> M.IfaceG M.Name -> REPL ()
showFunctorHelp _env _nameEnv name info =
  showSummary M.AFunctor name (M.ifsDoc ns) summary
  where
  ns      = M.ifNames info
  summary = (ifaceSummary (M.ifDefines info) ns)
                { msParams = [ (T.mpName p, T.mpIface p)
                             | p <- Map.elems (M.ifParams info)
                             ]
                }


showSigHelp ::
  M.IfaceDecls -> NameDisp -> M.Name -> T.ModParamNames -> REPL ()
showSigHelp _env _nameEnv name info =
  showSummary M.ASignature name (maybeToList (T.mpnDoc info))
    emptySummary
      { msTypes = Map.elems (T.mpnTypes info)
      , msVals  = Map.elems (T.mpnFuns info)
      , msConstraints = map P.thing (T.mpnConstraints info)
      }

--------------------------------------------------------------------------------
data ModSummary = ModSummary
  { msParams      :: [(P.Ident, P.ImpName M.Name)]
  , msConstraints :: [T.Prop]
  , msTypes       :: [T.ModTParam]
  , msVals        :: [T.ModVParam]
  , msMods        :: [ (M.Name, M.ModKind, [Text]) ]
  }

emptySummary :: ModSummary
emptySummary = ModSummary
  { msParams      = []
  , msConstraints = []
  , msTypes       = []
  , msVals        = []
  , msMods        = []
  }

showSummary :: M.ModKind -> M.Name -> [Text] -> ModSummary -> REPL ()
showSummary k name doc info =
  do rPutStrLn ""

     rPrint $ runDoc disp
        case k of
          M.AModule    ->
            vcat [ "Module" <+> pp name <+> "exports:"
                 , indent 2 $ vcat [ ppTPs, ppFPs ]
                 ]
          M.ASignature ->
            vcat [ "Interface" <+> pp name <+> "requires:"
                 , indent 2 $ vcat [ ppTPs, ppCtrs, ppFPs ]
                 ]
          M.AFunctor ->
            vcat [ "Parameterized module" <+> pp name <+> "requires:"
                 , indent 2 $ ppPs
                 , " ", "and exports:"
                 , indent 2 $ vcat [ ppTPs, ppFPs ]
                 ]

     doShowDocString doc

  where
  -- qualifying stuff is too noisy
  disp        = NameDisp \_ -> Just UnQualified

  withMaybeNest mb x =
    case mb of
      Nothing -> x
      Just d  -> vcat [x, indent 2 d]

  withDoc mb = withMaybeNest (pp <$> mb)
  withFix mb = withMaybeNest (text . ppFixity <$> mb)
  ppMany xs  = case xs of
                 [] -> mempty
                 _  -> vcat (" " : xs)

  ppPs = ppMany (map ppP (msParams info))
  ppP (x,y)
    | identIsNormal x = pp x <+> ": interface" <+> pp y
    | otherwise = "(anonymous parameter)"


  ppTPs  = ppMany (map ppTP (msTypes info))
  ppTP x = withDoc (T.mtpDoc x)
         $ hsep ["type", pp (T.mtpName x), ":", pp (T.mtpKind x)]

  ppCtrs = ppMany (map pp (msConstraints info))

  ppFPs  = ppMany (map ppFP (msVals info))
  ppFP x = withFix (T.mvpFixity x)
         $ withDoc (T.mvpDoc x)
         $ hsep [pp (T.mvpName x), ":" <+> pp (T.mvpType x) ]
--------------------------------------------------------------------------------




showTypeHelp ::
  M.ModContextParams -> M.IfaceDecls -> NameDisp -> T.Name -> REPL ()
showTypeHelp ctxparams env nameEnv name =
  fromMaybe (noInfo nameEnv name) $
  msum [ fromTySyn, fromNominal, fromTyParam ]

  where
  fromTySyn =
    do ts <- msum [ Map.lookup name (M.ifTySyns env)
                  , Map.lookup name
                      (T.mpnTySyn (M.modContextParamNames ctxparams))
                  ]
       return (doShowTyHelp nameEnv (pp ts) (T.tsDoc ts))

  fromNominal =
    do nt <- Map.lookup name (M.ifNominalTypes env)
       let decl kw =
             vcat
               [ kw <+> pp (T.ntName nt) <.> ":" <+> pp (T.kindOf nt)
               , ""
               , "Constructors:" <+>
                                   commaSep
                                   (map (pp . fst) (T.nominalTypeConTypes nt))
               ]
       case T.ntDef nt of
         T.Struct {} -> pure $ doShowTyHelp nameEnv (decl "newtype") (T.ntDoc nt)
         T.Enum {}   -> pure $ doShowTyHelp nameEnv (decl "enum") (T.ntDoc nt)
         T.Abstract  -> pure (primTypeHelp nt)

  primTypeHelp nt =
    do rPutStrLn ""
       rPrint $ runDoc nameEnv $ nest 4
              $ "primitive type" <+> pp (T.ntName nt)
                         <+> ":" <+> pp (T.kindOf nt)

       let vs = T.ntParams nt
       let cs = T.ntConstraints nt
       unless (null cs) $
         do let example = T.TNominal nt (map (T.TVar . T.tpVar) vs)
                ns = T.addTNames vs emptyNameMap
                rs = [ "•" <+> ppWithNames ns c | c <- cs ]
            rPutStrLn ""
            rPrint $ runDoc nameEnv $ indent 4 $
                        backticks (ppWithNames ns example) <+>
                        "requires:" $$ indent 2 (vcat rs)

       doShowFix (T.ntFixity nt)
       doShowDocString (T.ntDoc nt)

  allParamNames =
    case ctxparams of
      M.NoParams -> mempty
      M.FunctorParams fparams ->
        Map.unions
          [ (\x -> (Just p,x)) <$> T.mpnTypes (T.mpParameters ps)
          | (p, ps) <- Map.toList fparams
          ]
      M.InterfaceParams ps -> (\x -> (Nothing ,x)) <$> T.mpnTypes ps

  fromTyParam =
    do (x,p) <- Map.lookup name allParamNames
       pure do rPutStrLn ""
               case x of
                  Just src -> doShowParameterSource src
                  Nothing  -> pure ()
               let ty = "type" <+> pp name <+> ":" <+> pp (T.mtpKind p)
               rPrint (runDoc nameEnv (indent 4 ty))
               doShowDocString (T.mtpDoc p)


doShowTyHelp :: NameDisp -> Doc -> Maybe Text -> REPL ()
doShowTyHelp nameEnv decl doc =
  do rPutStrLn ""
     rPrint (runDoc nameEnv (nest 4 decl))
     doShowDocString doc

showConHelp :: M.IfaceDecls -> NameDisp -> P.PName -> T.Name -> REPL ()
showConHelp env nameEnv qname name =
  fromMaybe (noInfo nameEnv name) (Map.lookup name allCons)
  where
  allCons = foldr addCons mempty (M.ifNominalTypes env)
    where
    getDocs nt =
      case T.ntDef nt of
        T.Struct {} -> [ Nothing ]
        T.Enum cs   -> map (Just . T.ecDoc) cs
        T.Abstract  -> []

    addCons nt mp = foldr (addCon nt) mp
                      (zip (T.nominalTypeConTypes nt) (getDocs nt))
    addCon nt ((c,t),d) = Map.insert c $
      do rPutStrLn ""
         rPrint (runDoc nameEnv $ vcat
            [ "Constructor of" <+> pp (T.ntName nt)
            , indent 4 $ hsep [ pp qname, ":", pp t ]
            ])
         maybe (pure ()) doShowDocString d


showValHelp ::
  M.ModContextParams -> M.IfaceDecls -> NameDisp -> P.PName -> T.Name -> REPL ()

showValHelp ctxparams env nameEnv qname name =
  fromMaybe (noInfo nameEnv name)
            (msum [ fromDecl, fromParameter ])
  where
  fromDecl =
    do M.IfaceDecl { .. } <- Map.lookup name (M.ifDecls env)
       return $
         do rPutStrLn ""

            let property 
                  | P.PragmaProperty `elem` ifDeclPragmas = [text "property"]
                  | otherwise                             = []
            rPrint $ runDoc nameEnv
                   $ indent 4
                   $ hsep

                   $ property ++ [pp qname, colon, pp (ifDeclSig)]

            doShowFix $ ifDeclFixity `mplus`
                        (guard ifDeclInfix >> return P.defaultFixity)

            doShowDocString ifDeclDoc

  allParamNames =
    case ctxparams of
      M.NoParams -> mempty
      M.FunctorParams fparams ->
        Map.unions
          [ (\x -> (Just p,x)) <$> T.mpnFuns (T.mpParameters ps)
          | (p, ps) <- Map.toList fparams
          ]
      M.InterfaceParams ps -> (\x -> (Nothing,x)) <$> T.mpnFuns ps

  fromParameter =
    do (x,p) <- Map.lookup name allParamNames
       pure do rPutStrLn ""
               case x of
                 Just src -> doShowParameterSource src
                 Nothing -> pure ()
               let ty = pp name <+> ":" <+> pp (T.mvpType p)
               rPrint (runDoc nameEnv (indent 4 ty))
               doShowFix (T.mvpFixity p)
               doShowDocString (T.mvpDoc p)


doShowParameterSource :: P.Ident -> REPL ()
doShowParameterSource i =
  do rPutStrLn (Text.unpack msg)
     rPutStrLn ""
  where
  msg
    | identIsNormal i = "Provided by module parameter " <> P.identText i <> "."
    | otherwise       = "Provided by `parameters` declaration."


doShowDocString :: Foldable f => f Text -> REPL ()
doShowDocString doc =
  for_ doc $ \d ->
    rPutStrLn ('\n' : Text.unpack d)

ppFixity :: T.Fixity -> String
ppFixity f = "Precedence " ++ show (P.fLevel f) ++ ", " ++
               case P.fAssoc f of
                 P.LeftAssoc   -> "associates to the left."
                 P.RightAssoc  -> "associates to the right."
                 P.NonAssoc    -> "does not associate."

doShowFix :: Maybe T.Fixity -> REPL ()
doShowFix fx =
  case fx of
    Just f  -> rPutStrLn ('\n' : ppFixity f)
    Nothing -> return ()



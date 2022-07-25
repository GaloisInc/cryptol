{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
module Cryptol.REPL.Help (helpForNamed) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Data.List(intersperse)
import Control.Monad(when,guard,unless,msum,mplus)

import Cryptol.Utils.PP
import Cryptol.Utils.Ident(OrigName(..))
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Name as M
import qualified Cryptol.ModuleSystem.NamingEnv as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Interface as M
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.TypeCheck.PP(emptyNameMap,ppWithNames)

import Cryptol.REPL.Monad

helpForNamed :: P.PName -> REPL ()
helpForNamed qname =
  do fe <- getFocusedEnv
     let params = M.mctxParams fe
         env    = M.mctxDecls  fe
         rnEnv  = M.mctxNames  fe
         disp   = M.mctxNameDisp fe

         vNames = M.lookupListNS M.NSValue  qname rnEnv
         tNames = M.lookupListNS M.NSType   qname rnEnv
         mNames = M.lookupListNS M.NSModule qname rnEnv

     let helps = map (showTypeHelp params env disp) tNames ++
                 map (showValHelp params env disp qname) vNames ++
                 map (showModHelp env disp) mNames

         separ = rPutStrLn "            ---------"
     sequence_ (intersperse separ helps)

     when (null (vNames ++ tNames ++ mNames)) $
       rPrint $ "Undefined name:" <+> pp qname


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
showModuleHelp _env nameEnv name info =
  do rPrint $ runDoc nameEnv $ indent 4 $ vcat [ " ", ppM ]
     doShowDocString (M.ifsDoc info)

  where
  ppM = vcat [ "module" <+> pp name <+> "exports:"
             , indent 2 (vcat (map ppN (Set.toList (M.ifsPublic info))))
             ]
  ppN x = pp x


showFunctorHelp ::
  M.IfaceDecls -> NameDisp -> M.Name -> M.IfaceG M.Name -> REPL ()
showFunctorHelp env nameEnv name info =
  rPrint $ runDoc nameEnv
         $ vcat [ "`" <> pp name <> "` is a parameterized submodule." ]

showSigHelp ::
  M.IfaceDecls -> NameDisp -> M.Name -> T.ModParamNames -> REPL ()
showSigHelp _env _nameEnv name info =
  do rPutStrLn ""
     ppDoc (indent 4 ppS)
     case T.mpnDoc info of
       Just d -> do rPutStrLn ""
                    rPutStrLn (Text.unpack d)
       Nothing -> pure ()

  where
  -- qualifying stuff is too noisy
  disp        = NameDisp \_ -> Just UnQualified
  ppDoc d     = rPrint (runDoc disp d)

  ppS = vcat [ "interface" <+> pp name <+> "requires:"
             , indent 2 (vcat [ " ", ppTPs, ppCtrs, ppFPs ])
             ]

  withDoc mb x = case mb of
                   Nothing -> x
                   Just d  -> vcat [x, indent 2 (pp d)]

  ppTPs  = vcat (map ppTP (Map.elems (T.mpnTypes info)))
  ppTP x = withDoc (T.mtpDoc x)
         $ hsep ["type", pp (T.mtpName x), ":", pp (T.mtpKind x)]

  ppCtrs = case T.mpnConstraints info of
             [] -> mempty
             cs -> vcat [" ", "satisfying:"
                        , indent 2 (vcat (map ppCtr cs)), " "]
  ppCtr x = pp (P.thing x)

  ppFPs  = vcat (map ppFP (Map.elems (T.mpnFuns info)))
  ppFP x = withDoc (T.mvpDoc x)
         $ hsep [pp (T.mvpName x), ":" <+> pp (T.mvpType x) ]


showTypeHelp :: T.FunctorParams -> M.IfaceDecls -> NameDisp -> T.Name -> REPL ()
showTypeHelp mbParams env nameEnv name =
  fromMaybe (noInfo nameEnv name) $
  msum [ fromTySyn, fromPrimType, fromNewtype, fromTyParam ]

  where
  fromTySyn =
    do ts <- Map.lookup name (M.ifTySyns env)
       return (doShowTyHelp nameEnv (pp ts) (T.tsDoc ts))

  fromNewtype =
    do nt <- Map.lookup name (M.ifNewtypes env)
       let decl = pp nt $$ (pp name <+> text ":" <+> pp (T.newtypeConType nt))
       return $ doShowTyHelp nameEnv decl (T.ntDoc nt)

  fromPrimType =
    do a <- Map.lookup name (M.ifAbstractTypes env)
       pure $ do rPutStrLn ""
                 rPrint $ runDoc nameEnv $ nest 4
                        $ "primitive type" <+> pp (T.atName a)
                                   <+> ":" <+> pp (T.atKind a)

                 let (vs,cs) = T.atCtrs a
                 unless (null cs) $
                   do let example = T.TCon (T.abstractTypeTC a)
                                           (map (T.TVar . T.tpVar) vs)
                          ns = T.addTNames vs emptyNameMap
                          rs = [ "•" <+> ppWithNames ns c | c <- cs ]
                      rPutStrLn ""
                      rPrint $ runDoc nameEnv $ indent 4 $
                                  backticks (ppWithNames ns example) <+>
                                  "requires:" $$ indent 2 (vcat rs)

                 doShowFix (T.atFixitiy a)
                 doShowDocString (T.atDoc a)

  fromTyParam = Nothing -- XXX
{-
    do hasPs <- mbParams
       case hasPs of
         M.NewStyle {} -> undefined -- XXX
         M.OldStyle params ->
           do p <- Map.lookup name (M.ifParamTypes params)
              let uses c = T.TVBound (T.mtpParam p) `Set.member` T.fvs c
                  ctrs = filter uses (map P.thing (M.ifParamConstraints params))
                  ctrDoc = case ctrs of
                             []  -> []
                             [x] -> [pp x]
                             xs  -> [parens $ commaSep $ map pp xs]
                  decl = vcat $
                           [ text "parameter" <+> pp name <+> text ":"
                             <+> pp (T.mtpKind p) ]
                           ++ ctrDoc
              return $ doShowTyHelp nameEnv decl (T.mtpDoc p)
-}


doShowTyHelp :: NameDisp -> Doc -> Maybe Text -> REPL ()
doShowTyHelp nameEnv decl doc =
  do rPutStrLn ""
     rPrint (runDoc nameEnv (nest 4 decl))
     doShowDocString doc


doShowFix :: Maybe T.Fixity -> REPL ()
doShowFix fx =
  case fx of
    Just f  ->
      let msg = "Precedence " ++ show (P.fLevel f) ++ ", " ++
                 (case P.fAssoc f of
                    P.LeftAssoc   -> "associates to the left."
                    P.RightAssoc  -> "associates to the right."
                    P.NonAssoc    -> "does not associate.")

      in rPutStrLn ('\n' : msg)

    Nothing -> return ()


showValHelp ::
  T.FunctorParams -> M.IfaceDecls -> NameDisp -> P.PName -> T.Name -> REPL ()

showValHelp mbParams env nameEnv qname name =
  fromMaybe (noInfo nameEnv name)
            (msum [ fromDecl, fromNewtype, fromParameter ])
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

  fromNewtype =
    do _ <- Map.lookup name (M.ifNewtypes env)
       return $ return ()

  fromParameter = Nothing -- XXX
{-
    do hasPs <- mbParams
       case hasPs of
         M.NewStyle {} -> undefined -- XXX
         M.OldStyle params ->
           do p <- Map.lookup name (M.ifParamFuns params)
              return $
                do rPutStrLn ""
                   rPrint $ runDoc nameEnv
                          $ indent 4
                          $ text "parameter" <+> pp qname
                                             <+> colon
                                             <+> pp (T.mvpType p)

                   doShowFix (T.mvpFixity p)
                   doShowDocString (T.mvpDoc p)
-}


doShowDocString :: Maybe Text -> REPL ()
doShowDocString doc =
  case doc of
    Nothing -> pure ()
    Just d  -> rPutStrLn ('\n' : Text.unpack d)




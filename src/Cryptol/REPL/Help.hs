{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
module Cryptol.REPL.Help (helpForNamed) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Data.List(intersperse)
import Control.Monad(when,guard,unless,msum,mplus)

import Cryptol.Utils.PP
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
         sNames = M.lookupListNS M.NSSignature qname rnEnv

     let helps = map (showTypeHelp params env disp) tNames ++
                 map (showValHelp params env disp qname) vNames ++
                 map (showModHelp env disp) mNames ++
                 map (showSigHelp env disp) sNames

         separ = rPutStrLn "            ---------"
     sequence_ (intersperse separ helps)

     when (null (vNames ++ tNames ++ mNames ++ sNames)) $
       rPrint $ "Undefined name:" <+> pp qname


noInfo :: NameDisp -> M.Name -> REPL ()
noInfo nameEnv name =
  case M.nameInfo name of
    M.Declared m _ ->
      rPrint (runDoc nameEnv ("Name defined in module" <+> pp m))
    M.Parameter  -> rPutStrLn "// No documentation is available."


showModHelp :: M.IfaceDecls -> NameDisp -> M.Name -> REPL ()
showModHelp _env nameEnv x =
    rPrint $ runDoc nameEnv $ vcat [ "`" <> pp x <> "` is a module." ]
    -- XXX: show doc. if any




showSigHelp :: M.IfaceDecls -> NameDisp -> M.Name -> REPL ()
showSigHelp env nameEnv name =
  do rPrint $ runDoc nameEnv $ vcat [ "`" <> pp name <> "` is a signature." ]
     fromMaybe (noInfo nameEnv name)
       do s <- Map.lookup name (M.ifSignatures env)
          d <- M.ifParamDoc s
          pure (rPrint (pp d))
  -- XXX: show doc. if any, and maybe other stuff


showTypeHelp ::
  Maybe M.IfaceFunctorParams -> M.IfaceDecls -> NameDisp -> T.Name -> REPL ()
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

  fromTyParam =
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
  Maybe M.IfaceFunctorParams ->
    M.IfaceDecls -> NameDisp -> P.PName -> T.Name -> REPL ()

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

  fromParameter =
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


doShowDocString :: Maybe Text -> REPL ()
doShowDocString doc =
  case doc of
    Nothing -> pure ()
    Just d  -> rPutStrLn ('\n' : Text.unpack d)




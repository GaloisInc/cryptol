module Error (diagnostics) where

import Data.Text(Text)
import Data.Text qualified as Text
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Maybe(mapMaybe)
import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Diagnostics qualified as LSP
import Cryptol.Utils.PP
import Cryptol.Parser.Position
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Monad
import Cryptol.Parser qualified as P
import Cryptol.ModuleSystem.Renamer.Error qualified as R
import Cryptol.TypeCheck qualified as T
import Cryptol.Parser.NoPat qualified as NP 
import Cryptol.Parser.NoInclude qualified as NI
import Cryptol.Parser.ExpandPropGuards qualified as PG
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.InferTypes

import Position


-- | Render diagnostics.  The `Bool` is true if there's at least one error.
diagnostics ::
  Maybe ModuleError -> [ModuleWarning] ->
  (Bool, Map LSP.NormalizedUri LSP.DiagnosticsBySource)
diagnostics mbErr ws = (not (null errDs), LSP.partitionBySource <$> grp)
  where
  errDs = toDiag noExtra mbErr
  allDs = errDs ++ toDiag noExtra ws
  grp   = Map.fromListWith (++) [ (LSP.toNormalizedUri x,[y]) | (x,y) <- allDs ]


data Extra = Extra {
  fallbackRange :: [Range],
  nameMap :: Maybe T.NameMap
}

noExtra :: Extra
noExtra = Extra { fallbackRange = mempty, nameMap = mempty }


class Diag t where
  toDiag :: Extra -> t -> [(LSP.Uri, LSP.Diagnostic)]


instance Diag a => Diag (Maybe a) where
  toDiag fp = maybe [] (toDiag fp)

instance Diag a => Diag [a] where
  toDiag fp = concatMap (toDiag fp) 


instance Diag ModuleWarning where
  toDiag _ wa =
    case wa of
      TypeCheckWarnings nm ws ->
        [ mkWarn r (ppWithNames nm w) | (r,w) <- ws ]
      RenamerWarnings ws ->
        [ mkWarn r (pp w)
        | w <- ws
        , r <-
          case w of
            R.SymbolShadowed _ x xs -> map nameLoc (x:xs)
            R.UnusedName x -> [ nameLoc x ]
            R.PrefixAssocChanged _ _ r _ _ -> [ srcRange r ]
        ]

instance Diag ModuleError where
  toDiag mbFile err =
    case err of
      ModuleParseError _ _ e -> toDiag noExtra e

      RenamerErrors imp errs ->
        toDiag (noExtra { fallbackRange = importSourceLoc imp }) errs
      TypeCheckingFailed _ names errs ->
        [ di | (r,e) <- errs,
                let ex = Extra { fallbackRange = [r], nameMap = Just names }, 
                di <- toDiag ex e ]
                                     
      ModuleNotFound isrc _ _ ->
        [ mkErr r (pp err) | r <- importSourceLoc isrc ] 
      CantFindFile {} -> []
      BadUtf8 {} -> []
      OtherIOError {} -> []
      
      RecursiveModules imps ->
        [ mkErr r (pp err) | i <- imps, r <- importSourceLoc i ]
      
      NoPatErrors _ errs -> toDiag noExtra errs
      NoIncludeErrors _ errs -> toDiag noExtra errs
      ExpandPropGuardsError _ errs -> toDiag noExtra errs

      OtherFailure {} -> []
      ModuleNameMismatch _ lm -> [ mkErr (srcRange lm) (pp err) ]
      DuplicateModuleName {} -> []
      FFILoadErrors {} -> []
      ConfigLoadError _ -> []
      ErrorInFile _ e -> toDiag mbFile e

importSourceLoc :: ImportSource -> [Range]
importSourceLoc imp =
  case imp of
    FromModule {} -> []
    FromImport l -> [srcRange l]
    FromSigImport l -> [srcRange l]
    FromModuleInstance l -> [srcRange l]


instance Diag P.ParseError where
  toDiag _ err = [ mkErr loc (P.ppError err) ]
    where
    loc =
      case err of
        P.HappyError _ t -> srcRange t
        P.HappyErrorMsg rng _ -> rng
        P.HappyUnexpected fp mb _ ->
            case mb of
              Just t -> srcRange t
              Nothing -> point fp start
        P.HappyOutOfTokens fp pos -> point fp pos
   
point :: FilePath -> Position -> Range
point f p = Range { source = f, from = p, to = p }


instance Diag R.RenamerError where
  toDiag mb err = [ mkErr l (pp err) | l <- locs ]
    where
    locs =
      case err of
        R.MultipleSyms l _ -> [ srcRange l ]
        R.UnboundName _ l -> [ srcRange l ]
        R.OverlappingSyms ls -> map nameLoc ls
        R.WrongNamespace _ _ l -> [srcRange l ]
        R.FixityError l1 _ l2 _ -> [srcRange l1, srcRange l2]
        R.OverlappingRecordUpdate l1 l2 -> [srcRange l1, srcRange l2]
        R.InvalidDependency ds ->
            case mapMaybe R.depNameLoc ds of
              [] -> fallbackRange mb
              ls -> ls
        R.MultipleModParams _ rs -> rs
        R.InvalidFunctorImport _ ->  fallbackRange mb
        R.UnexpectedNest r _ -> [r]
        R.ModuleKindMismatch r _ _ _ -> [r]

instance Diag T.Error where
  toDiag extra e =
    case e of

      T.UnsolvedGoals gs -> grp T.UnsolvableGoals [ (goalRange g, g) | g <- gs ]
        
      T.UnsolvedDelayedCt dc -> grp mkD [ (goalRange g, g) | g <- dctGoals dc ]
        where mkD gs = T.UnsolvedDelayedCt dc { dctGoals = gs } 

      T.RepeatedTypeParameter _ rs -> [ mk r e | r <- rs ]
      
      T.OverlappingPat _ rs -> [ mk r e | r <- rs ]

      _ -> [ mk r e | r <- fallbackRange extra ]
        
    where
    mk r err = mkErr r (doPP err)

    doPP = maybe pp ppWithNames (nameMap extra)

    grp bld i =
      [ mk r (bld as) | (r,as) <- Map.toList $ 
                                  Map.fromListWith (++) [ (x,[y]) | (x,y) <- i ]]
            

instance Diag NP.Error where
  toDiag _ err =
    [ mkErr r (pp err)
    | r <-
      case err of
        NP.MultipleSignatures _ ls -> map srcRange ls
        NP.SignatureNoBind l _ -> [ srcRange l ]
        NP.PragmaNoBind l _ -> [ srcRange l ]
        NP.MultipleFixities _ rs -> rs
        NP.FixityNoBind l -> [srcRange l]
        NP.MultipleDocs _ rs -> rs
        NP.InvalidConstructorPattern r -> [r]
    ]

instance Diag NI.IncludeError where
  toDiag ex err =
    case err of
      NI.IncludeParseError pe -> toDiag ex pe
      NI.IncludeFailed l -> mk [ srcRange l ]
      NI.IncludeDecodeFailed l _ -> mk [ srcRange l ]
      NI.IncludeCycle ls -> mk (map srcRange ls)
    where
    mk rs = [ mkErr r (NI.ppIncludeError err) | r <- rs ]

instance Diag PG.Error where
  toDiag _ err =
    [ mkErr r (pp err)
    | r <-
      case err of
        PG.NoSignature l -> [ srcRange l ]
        PG.NestedConstraintGuard l -> [ srcRange l ]
    ]


mkErr :: Range -> Doc -> (LSP.Uri, LSP.Diagnostic)
mkErr r d = mkDiag LSP.DiagnosticSeverity_Error r (Text.pack (show d))

mkWarn :: Range -> Doc -> (LSP.Uri, LSP.Diagnostic)
mkWarn r d = mkDiag LSP.DiagnosticSeverity_Warning r (Text.pack (show d))

mkDiag ::
  LSP.DiagnosticSeverity -> Range -> Text -> (LSP.Uri, LSP.Diagnostic)
mkDiag sev cryRng msg = (uri, diag)
  where
  (uri, rng) = rangeToLSP cryRng 
  diag =
    LSP.Diagnostic{
      _range = rng,
      _severity = Just sev,
      _code  = Nothing,
      _codeDescription = Nothing,
      _source = Just "cryptol",
      _message = msg,
      _tags = Nothing,
      _relatedInformation = Nothing,
      _data_ = Nothing
    }
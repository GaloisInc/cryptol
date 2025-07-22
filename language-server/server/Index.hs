module Index (
  IndexDB,  -- XXX: Temporary
  DefInfo(..),
  ModDefInfo(..),
  RangeInfo(..),
  Thing(..),
  ExtraSemTokInfo(..),
  emptyIndexDB,
  updateIndexes,
  lookupPosition,
  lookupExtraSemToks,
  doLoadedModule
) where

import Data.Maybe(fromMaybe)
import Data.List(foldl')
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Lens((^.))
import Control.Monad(guard,mplus,void)

import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Protocol.Lens qualified as LSP

import Cryptol.Parser.Position
import Cryptol.TypeCheck.AST qualified as T
import Cryptol.TypeCheck.PP qualified as T
import Cryptol.TypeCheck.Subst qualified as T
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Env
import Cryptol.Utils.PP
import Cryptol.Utils.Ident

import Position
import Definitions


data IndexDB = IndexDB {
  allDefs :: Map Name DefInfo,
  -- ^ Information about names

  allModDefs :: Map ModName ModDefInfo,
  -- ^ Information about top-level modules

  posIndex :: Map ModulePath (ModIndex, Map Name (), Map ModName ())
  -- ^ Locations of identifiers in a module and definitions coming from this module
}

-- | Information about stuff in a single file
data ModIndex = ModIndex {
  modIndexHover :: Map Range (Thing Name ModName),
  modIndexFolds :: [Range]
}

instance Semigroup ModIndex where
  x <> y = ModIndex {
    modIndexHover = Map.union (modIndexHover x) (modIndexHover y),
    modIndexFolds = modIndexFolds x ++ modIndexFolds y
  }

-- | Something that we have info about
data Thing a b =
    NamedThing (RangeInfo a)    -- ^ A name
  | ModThing b                  -- ^ A module


data RangeInfo a = RangeInfo {
  rangeDef :: a,
  -- ^ Definition (or name of definition)

  rangeNameDisp :: NameDisp,
  -- ^ How to show names

  rangeType :: Maybe (T.NameMap, T.Schema),
  -- ^ Instantiated type at a particular call site

  rangeTArgs :: Maybe (T.NameMap, [T.Type])
  -- ^ Type parameters at call cite
}

mkRangeDef :: (NameDisp,Name) -> Maybe (T.NameMap, [T.Type]) -> RangeInfo Name
mkRangeDef (d,a) as =
  RangeInfo { rangeDef = a, rangeNameDisp = d, rangeType = Nothing, rangeTArgs = as }

instance PP a => PP (RangeInfo a) where
  ppPrec _ ri =
    fixNameDisp (rangeNameDisp ri)
    case rangeType ri of
      Just (nm,ty) ->
        vcat [
          "__" <> T.ppWithNames nm ty <> "__",
          "",
          pp (rangeDef ri)
        ]
      Nothing -> pp (rangeDef ri)

instance (PP a, PP b) => PP (Thing a b) where
  ppPrec _ th =
    case th of
      NamedThing x -> pp x
      ModThing x -> pp x

instance PP IndexDB where
  ppPrec _ db = ppFs -- , vcat [ pp x $$ indent 2 (pp y) | (x,y) <- Map.toList (allDefs db) ]]
    where
    ppFs = vcat (concatMap ppF (Map.toList (posIndex db)))
    ppF (f,(rs,_,_)) =
      case f of
        InFile _ -> [pp f $$ indent 2 (ppRs rs)]
        InMem {} -> []
    ppRs rs = vcat [ hcat [ppR r, ": ", pp n] | (r,n) <- Map.toList (modIndexHover rs) ]
    ppR r = hcat [ pp (from r), "--", pp (to r)]
    

-- | A DB with no information.
emptyIndexDB :: IndexDB
emptyIndexDB = IndexDB {
  allDefs = mempty,
  allModDefs = mempty,
  posIndex = mempty
}

data ExtraSemTokInfo = ExtraSemTokInfo {
  extraSemToks :: Range -> Maybe LSP.SemanticTokenTypes,
  extraFold    :: [Range]
}

noExtraSemTokInfo :: ExtraSemTokInfo
noExtraSemTokInfo = ExtraSemTokInfo {
  extraSemToks  = const Nothing,
  extraFold     = []
}

lookupExtraSemToks ::
  LSP.NormalizedUri -> IndexDB -> ExtraSemTokInfo
lookupExtraSemToks uri db =
  fromMaybe noExtraSemTokInfo
  do
    file <- LSP.fromNormalizedFilePath <$> LSP.uriToNormalizedFilePath uri
    (info,_,_) <- Map.lookup (InFile file) (posIndex db)
    pure
      ExtraSemTokInfo {
        extraSemToks = \rng ->
          do thing <- Map.lookup rng { source = file } (modIndexHover info)
             case thing of
               NamedThing a ->
                let nm = rangeDef a
                in Just
                  case nameNamespace nm of
                    NSValue ->
                      case nameInfo nm of
                        GlobalName {} -> LSP.SemanticTokenTypes_Function
                        LocalName {} -> LSP.SemanticTokenTypes_Variable
                    NSConstructor -> LSP.SemanticTokenTypes_EnumMember
                    NSType        -> LSP.SemanticTokenTypes_Type
                    NSModule      -> LSP.SemanticTokenTypes_Namespace
               ModThing _ -> pure LSP.SemanticTokenTypes_Namespace,
        extraFold = modIndexFolds info
      }
        
  

lookupPosition ::
  LSP.NormalizedUri -> LSP.Position -> IndexDB -> Either Int (LSP.Range, Thing DefInfo ModDefInfo)
lookupPosition uri pos db =
  do
    file <- step 1 $ LSP.uriToNormalizedFilePath uri
    (info,_,_) <- step 2 $ Map.lookup (InFile (LSP.fromNormalizedFilePath file)) (posIndex db)
    let l   = fromIntegral (pos ^. LSP.line) + 1
        c   = fromIntegral (pos ^. LSP.character)
        tgt = replPosition (l,c)
        tooEarly rng = to rng < tgt
    (r,i0) <- step 3 $ Map.lookupMin (Map.dropWhileAntitone tooEarly (modIndexHover info))
    step 4 $ guard (from r <= tgt && tgt <= to r)
    let rrange = snd (rangeToLSP r)
    case i0 of
      NamedThing i ->
        do
          let n = rangeDef i
          def <- step 5 $ Map.lookup n (allDefs db)
          def' <- case defSeeAlso def of
                    Just a | Just b <- Map.lookup a (allDefs db) ->
                      pure def { defDoc = defDoc b `mplus` defDoc def }
                    _ -> pure def
          let ty =
                do
                  (nm,ts)   <- rangeTArgs i
                  (_nm1, s) <- defType def'
                  let su = T.listParamSubst (zip (T.sVars s) ts)
                  pure (nm, T.tMono (T.apSubst su (T.sType s)))-- assumes fully applied

          pure (rrange, NamedThing i { rangeDef = def', rangeType = ty, rangeTArgs = Nothing })
      ModThing i ->
        do
          def <- step 5 $ Map.lookup i (allModDefs db)
          pure (rrange, ModThing def)
     
  where
  step n = maybe (Left n) Right

unload :: ModulePath -> IndexDB -> IndexDB
unload pa i =
  case Map.lookup pa (posIndex i) of
    Nothing -> i
    Just (_,nms,ms) ->
      IndexDB {
        allDefs = allDefs i `Map.difference` nms,
        allModDefs = allModDefs i `Map.difference` ms,
        posIndex = Map.delete pa (posIndex i)
      }

-- | Update indexes based on what's currently loaded
updateIndexes ::
  [LoadedEntity] {- ^ Loaded modules -} ->
  IndexDB {- ^ Current index -} ->
  IndexDB {- ^ Updated index -}
updateIndexes loaded ixes = foldl' updateIndex ix0 loaded
  where
  ix0 = foldl' (\i ent -> unload (withLoadedEntity ent lmFilePath) i) ixes loaded
  updateIndex cur ent =
    case ent of
      ALoadedModule lm -> doLoadedModule lm cur
      ALoadedFunctor lm -> doLoadedModule lm cur
      ALoadedInterface _li -> cur
        -- for now we skip these as there's noting interesting to report



-- | Add indexing information for this loaded module.
doLoadedModule :: LoadedModule -> IndexDB -> IndexDB
doLoadedModule lm cur =

  case lmRenamedModule lm of
    Just rm ->
      let uri         = lmFilePath lm
          tys         = getVarTypes emptyTCtxt (lmdModule (lmData lm)) emptyTIndex
          addTy n inf = inf { defType = Map.lookup n (defTys tys) }
          i           = rangedVars rm noCtxt emptyIndex
          defs        = Map.mapWithKey addTy (ixDefs i)
          targs       = exprTyArgs tys
          getTArgs r x  =
            do
              (y,_disp,nm,t) <- Map.lookup r targs
              guard (x == y)
              pure (nm,t)
          isNumLit (x,disp,nm,t) =
            do
              p <- asPrim x
              guard (p == prelPrim "number")
              pure (NamedThing (mkRangeDef (disp, x) (Just (nm,t))))
          locs = ModIndex {
                   modIndexHover = Map.unions
                      [ Map.fromList [ (r, NamedThing (mkRangeDef x (getTArgs r (snd x))))
                                     | (r,x) <- ixUse i ] 
                      , Map.fromList [ (r, ModThing x) | (r,x) <- ixMod i ]
                      , Map.mapMaybe isNumLit targs
                      ],
                    modIndexFolds = [ r | d <- Map.elems (ixDefs i), Just r <- [defFullRange d] ]
                  }
          modDefs = ixModDefs i
          jn (a,b,c) (x,y,z) = (a <> x, Map.union b y, Map.union c z)
      in IndexDB {
          posIndex = Map.insertWith jn uri (locs, void defs, void modDefs) (posIndex cur),
          allModDefs = Map.union modDefs (allModDefs cur),
          allDefs  = Map.union defs (allDefs cur)
      }
    Nothing -> cur





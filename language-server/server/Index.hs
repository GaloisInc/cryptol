module Index (
  IndexDB,
  DefInfo(..),
  RangeInfo(..),
  emptyIndexDB,
  updateIndexes,
  lookupPosition
) where

import Data.List(foldl')
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Lens((^.))
import Control.Monad(guard,mplus,void)

import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Protocol.Lens qualified as LSP

import Cryptol.Parser.Position
import Cryptol.Parser.AST
import Cryptol.TypeCheck.AST qualified as T
import Cryptol.TypeCheck.PP qualified as T
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Env
import Cryptol.Utils.PP

import Position
import Definitions

data IndexDB = IndexDB {
  allDefs :: Map Name DefInfo,
  -- ^ Information about names

  posIndex :: Map ModulePath (Map Range (RangeInfo Name), Map Name ())
  -- ^ Locations of identifiers in a module and definitions coming from this module
}

data RangeInfo a = RangeName a | RangeType (T.NameMap, T.Schema)

instance PP a => PP (RangeInfo a) where
  ppPrec _ ri =
    case ri of
      RangeName x -> pp x
      RangeType (x,t) -> T.ppWithNames x t

instance PP IndexDB where
  ppPrec _ db = vcat [ ppFs, vcat [ pp x $$ indent 2 (pp y) | (x,y) <- Map.toList (allDefs db) ]]
    where
    ppFs = vcat (map ppF (Map.toList (posIndex db)))
    ppF (f,(rs,_)) = pp f $$ indent 2 (ppRs rs)
    ppRs rs = vcat [ hcat [ppR r, ": ", ppN n] | (r,n) <- Map.toList rs ]
    ppR r = hcat [ pp (from r), "--", pp (to r)]
    ppN x =
      case x of
        RangeName nm -> pp nm
        RangeType (nm,ty) -> T.ppWithNames nm ty

-- | A DB with no information.
emptyIndexDB :: IndexDB
emptyIndexDB = IndexDB {
  allDefs = mempty,
  posIndex = mempty
}



lookupPosition ::
  LSP.Uri -> LSP.Position -> IndexDB -> Either Int (LSP.Range, RangeInfo DefInfo)
lookupPosition uri pos db =
  do
    file <- step 1 $ LSP.uriToFilePath uri
    (info,_) <- step 2 $ Map.lookup (InFile file) (posIndex db)
    let l   = fromIntegral (pos ^. LSP.line) + 1
        c   = fromIntegral (pos ^. LSP.character)
        tgt = replPosition (l,c)
        tooEarly rng = to rng < tgt
    (r,i) <- step 3 $ Map.lookupMin (Map.dropWhileAntitone tooEarly info)
    step 4 $ guard (from r <= tgt && tgt <= to r)
    case i of
      RangeName n ->
        do 
          def <- step 5 $ Map.lookup n (allDefs db)
          def' <- case defSeeAlso def of
                    Just a | Just b <- Map.lookup a (allDefs db) ->
                      pure def { defDoc = defDoc b `mplus` defDoc def }
                    _ -> pure def
          pure (snd (rangeToLSP r) , RangeName def')
      RangeType n -> pure ((snd (rangeToLSP r), RangeType n))
  where
  step n = maybe (Left n) Right

-- | Update indexes based on what's currently loaded
updateIndexes ::
  [LoadedEntity] {- ^ Loaded modules -} ->
  IndexDB {- ^ Current index -} ->
  IndexDB {- ^ Updated index -}
updateIndexes loaded ixes = foldl' updateIndex ixes loaded
  where
  updateIndex cur ent =
    case ent of
      ALoadedModule lm -> doLoadedModule lm cur
      ALoadedFunctor lm -> doLoadedModule lm cur
      ALoadedInterface _li -> cur
        -- for now we skip these as there's noting interesting to report


doLoadedModule :: LoadedModule -> IndexDB -> IndexDB
doLoadedModule lm cur =

  case entityFileInfo getTys lm of
    Just (uri, rm, tys) ->
      let i           = rangedVars (mDef rm) noCtxt emptyIndex
          addTy n inf = inf { defType = Map.lookup (Name n) tys }
          defs        = Map.mapWithKey addTy (ixDefs i)
          locs = [ (r, RangeName x) | (r,x) <- ixUse i ] ++
                 [ (r, RangeType (tctxNames ct,t))
                 | (Expr r,(ct,t)) <- Map.toList tys ]
      in IndexDB {
          posIndex = Map.insert uri (Map.fromList locs, void defs) (posIndex cur),
          allDefs  =
            Map.union defs
            case Map.lookup uri (posIndex cur) of
              Just (_,old) -> allDefs cur `Map.difference` old
              Nothing -> allDefs cur
      }
    Nothing -> cur
  where
  getTys m = getVarTypes emptyTCtxt (lmdModule m) mempty

entityFileInfo ::
  (a -> Map TKey (TCtxt, T.Schema)) ->
  LoadedModuleG a ->
  Maybe (ModulePath,Module Name, Map TKey (TCtxt, T.Schema))
entityFileInfo getTys lm =
  do rm <- lmRenamedModule lm
     pure (lmFilePath lm, rm, getTys (lmData lm))



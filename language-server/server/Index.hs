module Index (
  IndexDB,
  DefInfo(..),
  ModDefInfo(..),
  RangeInfo(..),
  Thing(..),
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

  posIndex :: Map ModulePath (Map Range (Thing Name ModName), Map Name (), Map ModName ())
  -- ^ Locations of identifiers in a module and definitions coming from this module
}

-- | Something that we have info about
data Thing a b =
    NamedThing (RangeInfo a)    -- ^ A name
  | ModThing b                  -- ^ A module


data RangeInfo a = RangeInfo {
  rangeDef :: a,
  -- ^ Definition (or name of definition)

  rangeType :: Maybe (T.NameMap, T.Schema),
  -- ^ Instantiated type at a particular call site

  rangeTArgs :: Maybe (T.NameMap, [T.Type])
  -- ^ Type parameters at call cite
}

mkRangeDef :: Name -> Maybe (T.NameMap, [T.Type]) -> RangeInfo Name
mkRangeDef a as =
  RangeInfo { rangeDef = a, rangeType = Nothing, rangeTArgs = as }

instance PP a => PP (RangeInfo a) where
  ppPrec _ ri =
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
      NamedThing x -> "name" <+> pp x
      ModThing x -> "module" <+> pp x

instance PP IndexDB where
  ppPrec _ db = vcat [ ppFs ] -- , vcat [ pp x $$ indent 2 (pp y) | (x,y) <- Map.toList (allDefs db) ]]
    where
    ppFs = vcat (map ppF (Map.toList (posIndex db)))
    ppF (f,(rs,_,_)) = pp f $$ indent 2 (ppRs rs)
    ppRs rs = vcat [ hcat [ppR r, ": ", pp n] | (r,n) <- Map.toList rs ]
    ppR r = hcat [ pp (from r), "--", pp (to r)]
    

-- | A DB with no information.
emptyIndexDB :: IndexDB
emptyIndexDB = IndexDB {
  allDefs = mempty,
  allModDefs = mempty,
  posIndex = mempty
}



lookupPosition ::
  LSP.Uri -> LSP.Position -> IndexDB -> Either Int (LSP.Range, Thing DefInfo ModDefInfo)
lookupPosition uri pos db =
  do
    file <- step 1 $ LSP.uriToFilePath uri
    (info,_,_) <- step 2 $ Map.lookup (InFile file) (posIndex db)
    let l   = fromIntegral (pos ^. LSP.line) + 1
        c   = fromIntegral (pos ^. LSP.character)
        tgt = replPosition (l,c)
        tooEarly rng = to rng < tgt
    (r,i0) <- step 3 $ Map.lookupMin (Map.dropWhileAntitone tooEarly info)
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


-- | Remove the given module from the index
unload :: ModulePath -> IndexDB -> IndexDB
unload mo i =
  case Map.lookup mo (posIndex i) of
    Nothing -> i
    Just (_, ours,ourMods) ->
      IndexDB {
        allDefs  = allDefs i `Map.difference` ours,
        allModDefs = allModDefs i `Map.difference` ourMods,
        posIndex = Map.delete mo (posIndex i)
      }

-- | Add indexing information for this loaded module.
doLoadedModule :: LoadedModule -> IndexDB -> IndexDB
doLoadedModule lm cur =

  case lmRenamedModule lm of
    Just rm ->
      let uri         = lmFilePath lm
          tys         = getTys (lmData lm)
          addTy n inf = inf { defType = Map.lookup n (defTys tys) }
          i           = rangedVars rm noCtxt emptyIndex
          defs        = Map.mapWithKey addTy (ixDefs i)
          targs       = exprTyArgs tys
          getTArgs r x  =
            do
              (y,nm,t) <- Map.lookup r targs
              guard (x == y)
              pure (nm,t)
          isNumLit (x,nm,t) =
            do
              p <- asPrim x
              guard (p == prelPrim "number")
              pure (NamedThing (mkRangeDef x (Just (nm,t))))
          locs = Map.unions
                  [ Map.fromList [ (r, NamedThing (mkRangeDef x (getTArgs r x)))
                                 | (r,x) <- ixUse i ]  
                  , Map.fromList [ (r, ModThing x) | (r,x) <- ixMod i ]
                  , Map.mapMaybe isNumLit targs
                  ]
          modDefs = ixModDefs i
          oldDefs = Map.lookup uri (posIndex cur)
      in IndexDB {
          posIndex = Map.insert uri (locs, void defs, void modDefs) (posIndex cur),
          allModDefs = Map.union modDefs
                       case oldDefs of
                         Just (_,_,old) -> allModDefs cur `Map.difference` old
                         Nothing -> allModDefs cur,
          allDefs  =
            Map.union defs
            case oldDefs of
              Just (_,old,_) -> allDefs cur `Map.difference` old
              Nothing -> allDefs cur
      }
    Nothing -> cur
  where
  getTys m = getVarTypes emptyTCtxt (lmdModule m) emptyTIndex




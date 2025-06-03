module Index (
  IndexDB,
  DefInfo(..),
  emptyIndexDB,
  updateIndexes,
  lookupPosition
) where

import Data.List(foldl')
import Data.Text(Text)
import Data.Map(Map)
import Data.Map qualified as Map
import Control.Lens((^.))
import Control.Monad(guard)

import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Protocol.Lens qualified as LSP

import Cryptol.Utils.RecordMap
import Cryptol.Parser.Position
import Cryptol.Parser.AST
import Cryptol.TypeCheck.AST qualified as T
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Env
import Cryptol.ModuleSystem.Interface
import Cryptol.Utils.PP

import Position
import Definitions

data IndexDB = IndexDB {
  allDefs :: Map Name DefInfo,
  -- ^ Information about names

  posIndex :: Map ModulePath (Map Range Name)
  -- ^ Locations of identifiers in a module
}

instance PP IndexDB where
  ppPrec _ db = vcat [ ppFs, vcat [ pp x $$ indent 2 (pp y) | (x,y) <- Map.toList (allDefs db) ]]
    where
    ppFs = vcat (map ppF (Map.toList (posIndex db)))
    ppF (f,rs) = pp f $$ indent 2 (ppRs rs)
    ppRs rs = vcat [ hcat [ppR r, ": ", pp n] | (r,n) <- Map.toList rs ]
    ppR r = hcat [ pp (from r), "--", pp (to r)]

-- | A DB with no information.
emptyIndexDB :: IndexDB
emptyIndexDB = IndexDB {
  allDefs = mempty,
  posIndex = mempty
}



lookupPosition :: LSP.Uri -> LSP.Position -> IndexDB -> Either Int (LSP.Range, DefInfo)
lookupPosition uri pos db =
  do
    file <- step 1 $ LSP.uriToFilePath uri
    info <- step 2 $ Map.lookup (InFile file) (posIndex db)
    let l   = fromIntegral (pos ^. LSP.line) + 1
        c   = fromIntegral (pos ^. LSP.character)
        tgt = replPosition (l,c)
        tooEarly rng = to rng < tgt
    (r,n) <- step 3 $ Map.lookupMin (Map.dropWhileAntitone tooEarly info)
    step 4 $ guard (from r <= tgt && tgt <= to r)
    def <- step 5 $ Map.lookup n (allDefs db)
    pure (snd (rangeToLSP r) , def)
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
      ALoadedModule lm ->
        case entityFileInfo lm of
          Just (uri, rm) ->
            let i  = rangedVars (mDef rm) noCtxt emptyIndex
                decls = ifDecls (ifDefines (lmdInterface (lmData lm)))
                addTy n inf = inf { defType = ifDeclSig <$> Map.lookup n decls }
                defs = Map.mapWithKey addTy (ixDefs i)
            in IndexDB {
                posIndex = Map.insert uri (Map.fromList (ixUse i)) (posIndex cur),
                allDefs  = Map.union defs (allDefs cur)
            }
          Nothing -> cur
      ALoadedFunctor lm -> cur -- XXX
      ALoadedInterface li -> cur  -- XXX

entityFileInfo :: LoadedModuleG a -> Maybe (ModulePath,Module Name)
entityFileInfo lm =
  do rm <- lmRenamedModule lm
     pure (lmFilePath lm, rm)







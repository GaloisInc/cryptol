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


-- | Information about a definition
data DefInfo = DefInfo {
  defRange :: Range,
  -- ^ Location of the definition (specifically, the name)

  defDoc   :: Maybe Text,
  -- ^ Documentation, if any

  defType  :: Maybe T.Schema
  -- ^ Type, if known
}

instance PP DefInfo where
  ppPrec _ di = vcat [
    maybe mempty pp (defDoc di),
    case defType di of
      Nothing -> mempty
      Just s -> vcat ["```",pp s,"```"]
    ]

lookupPosition :: LSP.Uri -> LSP.Position -> IndexDB -> Either Int (LSP.Range, DefInfo)
lookupPosition uri pos db =
  do
    file <- step 1 $ LSP.uriToFilePath uri
    info <- step 2 $ Map.lookup (InFile file) (posIndex db)
    let l   = fromIntegral (pos ^. LSP.line) + 1
        c   = fromIntegral (pos ^. LSP.character)
        tgt = replPosition (l,c)
        tooEarly rng = to rng < tgt
    (Range { from, to },n) <-
      step 3 $ Map.lookupMin (Map.dropWhileAntitone tooEarly info)
    step 4 $ guard (from <= tgt && tgt <= to)
    def <- step 5 $ Map.lookup n (allDefs db)
    let irange = LSP.mkRange (fromIntegral (line from - 1))
                             (fromIntegral (colOffset from))
                             (fromIntegral (line to - 1))
                             (fromIntegral (colOffset to))
    pure (irange, def)
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









--------------------------------------------------------------------------------
-- Collect definitions and variable uses

class RangedVars t where
  rangedVars ::
    t -> Ctxt -> Index -> Index

data Ctxt = Ctxt {
  curRange :: Maybe Range,
  curDoc   :: Maybe Text
}

data Index = Index {
  ixDefs :: Map Name DefInfo,
  -- ^ Things that are defined in this file (XXX: nested modules, locals).

  ixUse  :: [(Range,Name)]
  -- ^ Ranges in the file containing name uses.
}

emptyIndex :: Index
emptyIndex = Index { ixDefs = mempty, ixUse = [] }

noCtxt :: Ctxt
noCtxt = Ctxt { curRange = Nothing, curDoc = Nothing }


instance (RangedVars a, RangedVars b) => RangedVars (a,b) where
  rangedVars (a,b) mbRange = rangedVars a mbRange . rangedVars b mbRange 

instance RangedVars a => RangedVars [a] where
  rangedVars xs =
    case xs of
        []       -> const id
        x : more -> rangedVars (x,more)

instance RangedVars a => RangedVars (Maybe a) where
  rangedVars mb =
    case mb of
      Nothing -> const id
      Just a  -> rangedVars a

instance RangedVars a => RangedVars (Located a) where
  rangedVars lt ctx = rangedVars (thing lt) ctx { curRange = Just (srcRange lt) }

newtype Use = Use Name

instance RangedVars Use where
  rangedVars (Use a) ctx rest =
    case nameInfo a of
      GlobalName SystemName _ -> rest
      GlobalName UserName _ ->
        case curRange ctx of
          Nothing -> rest
          Just r  -> rest { ixUse = (r,a) : ixUse rest }
      LocalName ns i -> rest -- XXX, track current top decl

newtype Def = Def Name

instance RangedVars Def where
  rangedVars (Def a) ctx rest =
    case nameInfo a of
      GlobalName SystemName _ -> rest
      GlobalName UserName _ -> rest { ixDefs = Map.insert a info (ixDefs rest),
                                      ixUse = (r,a) : ixUse rest }
        where
        r = nameLoc a
        info = DefInfo {
          defRange = r,
          defDoc   = curDoc ctx,
          defType  = Nothing
        }
      LocalName ns i -> rest -- XXX: locals


--------------------------------------------------------------------------------

instance RangedVars (ModuleDefinition Name) where
  rangedVars mdef =
    case mdef of
      NormalModule tds -> rangedVars tds
      FunctorInstance f as is -> const id -- XXX
      InterfaceModule sig -> const id -- XXX

instance RangedVars (TopDecl Name) where
  rangedVars td =
    case td of
      Decl d -> rangedVars d
      DPrimType pt -> rangedVars pt
      _ -> const id -- XXX
      
      {-
  | TDNewtype (TopLevel (Newtype name)) -- ^ @newtype T as = t
  | TDEnum (TopLevel (EnumDecl name))   -- ^ @enum T as = cons@
  | Include (Located FilePath) -- ^ @include File@ (until NoInclude)

  | DParamDecl Range (Signature name)   -- ^ @parameter ...@ (parser only)

  | DModule (TopLevel (NestedModule name))      -- ^ @submodule M where ...@
  | DImport (Located (ImportG (ImpName name)))  -- ^ @import X@
  | DModParam (ModParam name)                   -- ^ @import interface X ...@
  | DInterfaceConstraint (Maybe (Located Text)) (Located [Prop name]) -}


instance RangedVars (PrimType Name) where
  rangedVars pt = rangedVars (Def <$> primTName pt, snd (primTCts pt))


instance RangedVars a => RangedVars (TopLevel a) where
  rangedVars a ctx = rangedVars (tlValue a) ctx { curDoc = thing <$> tlDoc a }

instance RangedVars (UpdField Name) where
  rangedVars (UpdField _ _ e) = rangedVars e
instance RangedVars (Schema Name) where
  rangedVars (Forall _ ps ts mbR) ctx = rangedVars (ps,ts) ctx'
    where ctx' = maybe ctx (\r -> ctx { curRange = Just r }) mbR

instance RangedVars (Prop Name) where
  rangedVars (CType t) = rangedVars t

instance RangedVars (Type Name) where
  rangedVars ty =
    case ty of
      TFun t1 t2 -> rangedVars (t1,t2)
      TSeq a b   -> rangedVars (a,b)
      TBit       -> const id
      TNum {}    -> const id
      TChar {}   -> const id
      TUser n ts -> rangedVars (Use n, ts)
      TTyApp xs -> rangedVars (map value xs)
      TRecord r -> rangedVars (map (uncurry Located) (recordElements r)) 
      TTuple ts -> rangedVars ts
      TWild     -> const id
      TLocated t r -> rangedVars (Located r t)
      TParens t _  -> rangedVars t
      TInfix x op _ y -> rangedVars (x,(Use <$> op, y))

instance RangedVars (TypeInst Name) where
  rangedVars ti =
    case ti of
      NamedInst n -> rangedVars (value n)
      PosInst t -> rangedVars t

instance RangedVars (Pattern Name) where
  rangedVars pat =
    case pat of
      PVar n -> rangedVars (Def <$> n)
      PWild -> const id
      PTuple ps -> rangedVars ps
      PRecord r -> rangedVars (map (uncurry Located) (recordElements r))
      PList ps -> rangedVars ps
      PTyped p t -> rangedVars (p,t)
      PSplit p1 p2 -> rangedVars (p1,p2)
      PCon c ps -> rangedVars (Use <$> c, ps)
      PLocated p r -> rangedVars (Located r p)

instance RangedVars (Bind Name) where
  rangedVars b ctx =
    rangedVars (Def <$> bName b) ctx1 .
    rangedVars (bParams b, (bDef b, bSignature b)) ctx2
      where
      ctx1 = ctx { curDoc = thing <$> bDoc b }
      ctx2 = ctx { curDoc = Nothing }

instance RangedVars (BindParams Name) where
  rangedVars bps =
    case bps of
      PatternParams ps -> rangedVars ps
      DroppedParams {} -> const id

instance RangedVars (BindDef Name) where
  rangedVars bd =
    case bd of
      DPrim -> const id
      DForeign _ i -> rangedVars i
      DImpl i -> rangedVars i

instance RangedVars (BindImpl Name) where
  rangedVars impl =
    case impl of
      DExpr e -> rangedVars e
      DPropGuards pg -> rangedVars pg

instance RangedVars (PropGuardCase Name) where
  rangedVars (PropGuardCase a b) = rangedVars (a,b)

instance RangedVars (Match Name) where
  rangedVars ma =
    case ma of
      Match p e -> rangedVars (p,e)
      MatchLet b -> rangedVars b

instance RangedVars (Expr Name) where
  rangedVars expr  =
    case expr of
      EVar n      -> rangedVars (Use n)
      ELit {}     -> const id
      EGenerate e -> rangedVars e
      ETuple es   -> rangedVars es
      ERecord r   -> rangedVars (map (uncurry Located) (recordElements r))
      ESel e _    -> rangedVars e 
      EUpd mbE fs -> rangedVars (mbE,fs)
      EList es    -> rangedVars es
      EFromTo a b c d -> rangedVars (a,(b,(c,d)))
      EFromToBy _ a b c d -> rangedVars (a,(b,(c,d)))
      EFromToDownBy _ a b c d -> rangedVars (a,(b,(c,d)))
      EFromToLessThan a b c -> rangedVars (a,(b,c))
      EInfFrom a b -> rangedVars (a,b)
      EComp e ms -> rangedVars (e,ms)
      EApp e1 e2 -> rangedVars (e1,e2)
      EAppT e t -> rangedVars (e,t)
      EIf e1 e2 e3 -> rangedVars (e1,(e2,e3))
      ECase e cs -> rangedVars (e,cs)
      EWhere e d -> rangedVars (e,d)
      ETyped e t -> rangedVars (e,t)
      ETypeVal t -> rangedVars t
      EFun _ ps e -> rangedVars (ps,e)
      ELocated e r -> rangedVars (Located r e)
      ESplit e -> rangedVars e
      EParens e -> rangedVars e
      EInfix e1 op _ e2 -> rangedVars (e1,(Use <$> op, e2))
      EPrefix _ e -> rangedVars e
  

instance RangedVars (CaseAlt Name) where
  rangedVars (CaseAlt p e) = rangedVars (p,e)

instance RangedVars (Decl Name) where
  rangedVars decl =
    case decl of
      DSignature {} -> const id
      DFixity {} -> const id
      DPragma {} -> const id
      DPatBind {} -> const id

      DBind b -> rangedVars b
      DRec bs -> rangedVars bs
      DType t -> rangedVars t
      DProp t -> rangedVars t        
      DLocated d r -> rangedVars (Located r d)

instance RangedVars (TySyn Name) where
  rangedVars (TySyn n _ _ t) = rangedVars (Def <$> n, t)

instance RangedVars (PropSyn Name) where
  rangedVars (PropSyn n _ _ t) = rangedVars (Def <$> n, t)
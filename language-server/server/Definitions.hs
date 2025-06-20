module Definitions where

import Data.Text(Text)
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Maybe(fromMaybe)

import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap
import Cryptol.Utils.Ident
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.TypeCheck.AST qualified as T
import Cryptol.TypeCheck.PP qualified as T
import Cryptol.Parser.Position

-- | Information about a definition
data DefInfo = DefInfo {
  defName  :: !Name,
  -- ^ The name of the definition

  defSeeAlso :: !(Maybe Name),
  -- ^ A related name, for example name in functor or name in interface.
  -- See `Index` for how it used (e.g., we use the doc from this name, if any)

  defRange :: Range,
  -- ^ Location of the definition (specifically, the name)

  defDoc   :: Maybe Text,
  -- ^ Documentation, if any

  defType  :: Maybe (T.NameMap, T.Schema)
  -- ^ Type, if known
}

-- | Information about a top-level module
data ModDefInfo = ModDefInfo {
  modDefRange :: Range,
  modDefDoc :: Maybe Text
}

instance PP DefInfo where
  ppPrec _ di = vcat [
    case defType di of
      Nothing -> mempty
      Just (nms,s) -> "__" <> pp (nameIdent (defName di)) <> "__: "
        <> T.ppWithNames nms s,
    "",
    maybe mempty pp (defDoc di),
    "",
    case asOrigName (defName di) of
      Just og  -> "*Defined in `" <> pp nm <> "`*"
        where
        m = ogModule og
        nm = case ogFromParam og of
                Just i -> Nested m i
                Nothing -> m
      Nothing -> "*Local definition*"
    ]

instance PP ModDefInfo where
  ppPrec _ mo =
    vcat [
      "Top-level module",
      "",
      maybe mempty pp (modDefDoc mo)
    ]
      

-- | Collect the types of declared variables.
-- Assumes all variables have distinct names
class GetVarTypes t where
  getVarTypes :: TCtxt -> t -> TIndex -> TIndex

-- | Various type information we collect.
data TIndex = TIndex {
  defTys :: Map Name (T.NameMap, T.Schema),
  -- ^ Types of names

  exprTyArgs :: Map Range (Name, NameDisp, T.NameMap, [T.Type])
  -- ^ Type arguments for various occurances of names 
}

emptyTIndex :: TIndex
emptyTIndex = TIndex { defTys = mempty, exprTyArgs = mempty }

addDefTy :: TCtxt -> Name -> T.Schema -> TIndex -> TIndex
addDefTy c x t i = i {
  defTys = Map.insert x (tctxNames c, t) (defTys i)
}

addTyArgs :: TCtxt -> Name -> TIndex -> TIndex
addTyArgs c x i =
  case tctxRange c of
    Just r
      | nameSrc x == UserName && not (null as) ->
        i { exprTyArgs = Map.insert r (x, tctxCurDisp c, tctxNames c, as) (exprTyArgs i) }
      where
      as = tctxTApp c

    _ -> i
     


-- | Context while collecting type information
data TCtxt = TCtxt {
  tctxPP    :: PPCfg,         -- ^ Global pretty printing options
  tctxCurDisp :: NameDisp,    -- ^ Display fore current definition
  tctxScopes :: Map ModPath NameDisp, -- ^ Display for each module
  tctxRange :: Maybe Range,   -- ^ Where are we
  tctxNames :: T.NameMap,     -- ^ How to pretty print type variables
  tctxTApp :: [T.Type]        -- ^ Type arguments (for type applications)
}

emptyTCtxt :: TCtxt 
emptyTCtxt = TCtxt { tctxPP = defaultPPCfg, tctxCurDisp = EmptyNameDisp, tctxScopes = mempty, tctxRange = Nothing, tctxNames = mempty, tctxTApp = [] }

addTNames :: [T.TParam] -> TCtxt -> TCtxt
addTNames xs t = t { tctxNames = T.addTNames cfg xs (tctxNames t) }
  where cfg = (tctxPP t) { ppcfgNameDisp = tctxCurDisp t }

-- | Adpat context to given definition
inDecl :: Name -> TCtxt -> TCtxt
inDecl x nm =
  fromMaybe nm
  do
    pa <- nameModPathMaybe x
    disp <- Map.lookup pa (tctxScopes nm)
    pure nm { tctxCurDisp = disp }


instance (GetVarTypes a, GetVarTypes b) => GetVarTypes (a,b) where
  getVarTypes nm (a,b) = getVarTypes nm a . getVarTypes nm b

instance (GetVarTypes a) => GetVarTypes (Maybe a) where
  getVarTypes nm = maybe id (getVarTypes nm)

instance (GetVarTypes a) => GetVarTypes [a] where
  getVarTypes nm xs =
    case xs of
      [] -> id
      x : ys -> getVarTypes nm (x,ys)


-- | Get the ModPath for the name of amodule
class AsModPath name where
  asModPath :: name -> ModPath

instance AsModPath Name where
  asModPath = nameModPath

instance AsModPath ModName where
  asModPath = TopModule

instance AsModPath name => GetVarTypes (T.ModuleG name) where
  getVarTypes nm mo =
    getVarTypes nm2 (Map.elems (T.mParamFuns mo), 
                    (Map.elems (T.mFunctors mo),
                    (T.mDecls mo,
                     Map.elems (T.mNominalTypes mo))))
    where
    nm1 = addTNames (map T.mtpParam (Map.elems (T.mParamTypes mo))) nm
    nm2 = nm1 {
      tctxScopes =
        Map.fromList $
          (asModPath (T.mName mo), toNameDisp (T.mInScope mo)) :
          [ (asModPath x, toNameDisp (T.smInScope y))
          | (x,y) <- Map.toList (T.mSubmodules mo) ]
      }


instance GetVarTypes T.ModVParam where
  getVarTypes nm mp = addDefTy nm (T.mvpName mp) (T.mvpType mp)

instance GetVarTypes T.DeclGroup where
  getVarTypes nm = getVarTypes nm . T.groupDecls

instance GetVarTypes T.Decl where
  getVarTypes nm d =
    addDefTy nm1 (T.dName d) (T.dSignature d) .
    case T.dDefinition d of
      T.DPrim         -> id
      T.DForeign _ i  -> getVarTypes nm1 i
      T.DExpr e       -> getVarTypes nm1 e
    where
    nm1 = inDecl (T.dName d) nm


instance GetVarTypes T.Expr where
  getVarTypes nm expr =
    case expr of
      T.ETuple es -> getVarTypes nm es
      T.EList es _ -> getVarTypes nm es
      T.ERec es -> getVarTypes nm (recordElements es)
      T.ESel e _ -> getVarTypes nm e
      T.ESet _ e1 _ e2 -> getVarTypes nm (e1,e2)                       
      T.EIf e1 e2 e3 -> getVarTypes nm (e1,(e2,e3))
      T.ECase e ps d -> getVarTypes nm (e,(Map.elems ps,d))
      T.EComp _ _ e m -> getVarTypes nm (e,m)
      T.EVar x ->  addTyArgs nm x
      T.ETAbs t e -> getVarTypes (addTNames [t] nm) e
      T.ETApp e t   -> getVarTypes nm1 e
        where nm1 = nm { tctxTApp = t : tctxTApp nm }
      T.EApp e1 e2  -> getVarTypes nm (e1,e2)
      T.EAbs x t e  -> getVarTypes nm e . addDefTy nm x (T.tMono t)
      T.ELocated r e -> getVarTypes nm1 e
        where nm1 = nm { tctxRange = Just r }
      T.EProofAbs _ e -> getVarTypes nm e
      T.EProofApp e -> getVarTypes nm e
      T.EWhere e ds     -> getVarTypes nm (e,ds)
      T.EPropGuards gs _ -> getVarTypes nm (map snd gs)
    
instance GetVarTypes T.CaseAlt where
  getVarTypes nm (T.CaseAlt xs e) =
    getVarTypes nm e . flip (foldr (\(x,t) -> addDefTy nm x (T.tMono t))) xs

instance GetVarTypes T.Match where
  getVarTypes nm m =
    case m of
      T.From x _ t e -> getVarTypes nm e . addDefTy nm x (T.tMono t)
      T.Let d -> getVarTypes nm d

instance GetVarTypes T.NominalType where
  getVarTypes nm nom = flip (foldr (uncurry (addDefTy nm2))) cons 
    where
    cons = T.nominalTypeConTypes nom
    nm1  = inDecl (T.ntName nom) nm
    nm2  = addTNames (T.ntParams nom) nm1


--------------------------------------------------------------------------------

class RangedVars t where
  rangedVars ::
    t -> Ctxt -> Index -> Index

data Ctxt = Ctxt {
  curNamingEnv  :: NameDisp,
  curRange      :: Maybe Range,
  curDoc        :: Maybe Text
}

data Index = Index {
  ixDefs :: Map Name DefInfo,
  -- ^ Things that are defined in this file.

  ixUse  :: [(Range,(NameDisp,Name))],
  -- ^ Ranges in the file containing name uses.

  ixModDefs :: Map ModName ModDefInfo,
  -- ^ Top-level modules defines in this file.

  ixMod  :: [(Range,ModName)]
  -- ^ Ranged in the file referring to top-level modules
}

emptyIndex :: Index
emptyIndex = Index { ixDefs = mempty, ixUse = [], ixModDefs = mempty, ixMod = [] }

noCtxt :: Ctxt
noCtxt = Ctxt { curNamingEnv = mempty, curRange = Nothing, curDoc = Nothing }

instance PP Index where
  ppPrec _ i =
    vcat [
      "Uses",
      vcat [ pp r <+> "module" <+> pp m | (r,m) <- ixMod i ],
      vcat [ pp r <+> "name" <+> fixNameDisp di (pp n) | (r,(di,n)) <- ixUse i ],
      "End uses"
    ]


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
    case nameSrc a of
      SystemName -> rest
      _ ->
        case curRange ctx of
          Nothing -> rest
          Just r  -> rest { ixUse = (r,(curNamingEnv ctx,a)) : ixUse rest }

instance RangedVars ModName where
  rangedVars m ctx rest =
    case curRange ctx of
      Just r | modNameIsNormal m -> rest { ixMod = (r,m) : ixMod rest }
      _ -> rest


newtype Def = Def Name
data Def' = Def' Bool Name Name
newtype ModDef = ModDef (Located ModName)



addDef :: Bool -> Maybe Name -> Name -> Ctxt -> Index -> Index
addDef addUse also nm ctx rest =
    case nameSrc nm of
      SystemName -> rest
      _ -> rest {
        ixDefs = Map.insert nm info (ixDefs rest),
        ixUse = if addUse then (rng,(curNamingEnv ctx, nm)) : ixUse rest else ixUse rest
      }
    where
    rng =
      case also of
        Nothing -> nameLoc nm
        Just r  -> nameLoc r

    blankInfo = DefInfo {
      defName  = nm,
      defSeeAlso = also,
      defRange = rng,
      defDoc   = Nothing,
      defType  = Nothing  -- added later
    }
    info =
      case nameInfo nm of 
        GlobalName {} -> blankInfo { defDoc = curDoc ctx }
        _             -> blankInfo



instance RangedVars Def' where
  rangedVars (Def' use rel a) = addDef use (Just rel) a


instance RangedVars Def where
  rangedVars (Def x) = addDef True Nothing x

instance RangedVars ModDef where
  rangedVars (ModDef m) ctx i
    | modNameIsNormal (thing m) =
      i { ixModDefs = Map.insert (thing m) info (ixModDefs i),
          ixMod = (srcRange m, thing m) : ixMod i }
    | otherwise = i
    where
    info = ModDefInfo {
      modDefRange = srcRange m,
      modDefDoc   = curDoc ctx
    }


--------------------------------------------------------------------------------
instance RangedVars (Module Name) where
  rangedVars mo ctxt = rangedVars (ModDef (mName mo)) ctxt1
                     . rangedVars (mDef mo) ctxt2
    where
    ctxt1 = ctxt { curDoc = thing <$> mDocTop mo }
    ctxt2 = ctxt { curNamingEnv = toNameDisp (mInScope mo) }
 
instance RangedVars (ModuleDefinition Name) where
  rangedVars mdef =
    case mdef of
      NormalModule tds -> rangedVars tds
      FunctorInstance f as is -> rangedVars (f,(as, map mk (Map.toList is)))
        where mk (x,y) = Def' False x y
      InterfaceModule sig -> rangedVars sig

instance RangedVars (ModuleInstanceArgs Name) where
  rangedVars ma =
    case ma of
      DefaultInstArg a -> rangedVars a
      DefaultInstAnonArg a -> rangedVars a
      NamedInstArgs as -> rangedVars as

instance RangedVars (ModuleInstanceArg Name) where
  rangedVars a =
    case a of
      ModuleArg i -> rangedVars i
      ParameterArg {} -> const id
      AddParams {} -> const id

instance RangedVars (ModuleInstanceNamedArg Name) where
  rangedVars (ModuleInstanceNamedArg _ x) = rangedVars x

instance RangedVars (TopDecl Name) where
  rangedVars td =
    case td of
      Decl d -> rangedVars d
      DPrimType pt -> rangedVars pt
      TDNewtype nt -> rangedVars nt
      TDEnum en -> rangedVars en
      DInterfaceConstraint _ xs -> rangedVars xs
      DModule nm -> rangedVars nm
      DImport i -> rangedVars i
      DModParam mp -> rangedVars mp
      DParamDecl r s -> \ctx -> rangedVars s ctx { curRange = Just r }
      Include {} -> const id

instance RangedVars (Signature Name) where
  rangedVars sd =
    rangedVars
      (sigImports sd,
      (sigTypeParams sd,
      (sigConstraints sd,
      (sigDecls sd,
       sigFunParams sd))))

instance RangedVars (SigDecl Name) where
  rangedVars sd ctx =
    case sd of
      SigTySyn ts d -> rangedVars ts ctx { curDoc = d }
      SigPropSyn ps d -> rangedVars ps ctx { curDoc = d }

instance RangedVars (ParameterType Name) where
  rangedVars pt ctx =
    rangedVars (Def <$> ptName pt) ctx { curDoc = thing <$> ptDoc pt }

instance RangedVars (ParameterFun Name) where
  rangedVars pf ctx =
    rangedVars (pfSchema pf) ctx .
    rangedVars (Def <$> pfName pf) ctx { curDoc = thing <$> pfDoc pf }

instance RangedVars (ModParam Name) where
  rangedVars mp = rangedVars (mpSignature mp, map mk (Map.toList (mpRenaming mp)))
    where
    mk (k,v) = Def' True v k

instance RangedVars (ImpName Name) where
  rangedVars imp =
    case imp of
      ImpNested n -> rangedVars (Use n)
      ImpTop m    -> rangedVars m

instance RangedVars (ImportG (ImpName Name)) where
  rangedVars imp = rangedVars (iModule imp)

instance RangedVars (NestedModule Name) where
  rangedVars (NestedModule nm) ctx = rangedVars (Def <$> mName nm, mDef nm) ctx1
    where ctx1 = ctx { curNamingEnv = toNameDisp (mInScope nm) }

instance RangedVars (Newtype Name) where
  rangedVars nt =
    rangedVars (Def <$> nm, (con, map (uncurry Located) (recordElements (nBody nt))))
    where
    nm = nName nt
    con = Def (nConName nt) <$ nm

instance RangedVars (EnumDecl Name) where
  rangedVars ed = rangedVars (Def <$> eName ed, eCons ed)

instance RangedVars (EnumCon Name) where
  rangedVars c = rangedVars (Def <$> ecName c, ecFields c)


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
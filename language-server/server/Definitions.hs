{-# LANGUAGE InstanceSigs #-}
module Definitions where

import Data.Text(Text)
import Data.Map(Map)
import Data.Map qualified as Map

import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST qualified as T
import Cryptol.TypeCheck.PP qualified as T
import Cryptol.Parser.Position

-- | Information about a definition
data DefInfo = DefInfo {
  defName  :: !Name,
  -- ^ The name of the definition

  defRange :: Range,
  -- ^ Location of the definition (specifically, the name)

  defDoc   :: Maybe Text,
  -- ^ Documentation, if any

  defType  :: Maybe (T.NameMap, T.Schema)
  -- ^ Type, if known
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
    case nameModPathMaybe (defName di) of
      Just p  -> "*Defined in `" <> pp p <> "`*"
      Nothing -> "*Local definition*"
    ]

-- | Collect the types of declared variables.
-- Assumes all variables have distinct names
class GetVarTypes t where
  getVarTypes ::
    T.NameMap -> t -> Map Name (T.NameMap, T.Schema) -> Map Name (T.NameMap, T.Schema)

instance (GetVarTypes a, GetVarTypes b) => GetVarTypes (a,b) where
  getVarTypes nm (a,b) = getVarTypes nm a . getVarTypes nm b

instance (GetVarTypes a) => GetVarTypes (Maybe a) where
  getVarTypes nm = maybe id (getVarTypes nm)

instance (GetVarTypes a) => GetVarTypes [a] where
  getVarTypes nm xs =
    case xs of
      [] -> id
      x : ys -> getVarTypes nm (x,ys)

instance GetVarTypes (T.ModuleG name) where
  getVarTypes nm mo = getVarTypes nm (T.mDecls mo, Map.elems (T.mNominalTypes mo))


instance GetVarTypes T.DeclGroup where
  getVarTypes nm = getVarTypes nm . T.groupDecls

instance GetVarTypes T.Decl where
  getVarTypes nm d =
    Map.insert (T.dName d) (nm, T.dSignature d) .
    case T.dDefinition d of
      T.DPrim         -> id
      T.DForeign _ i  -> getVarTypes nm i
      T.DExpr e       -> getVarTypes nm e

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
      T.EVar _ -> id
      T.ETAbs t e -> getVarTypes (T.addTNames [t] nm) e
      T.ETApp e _   -> getVarTypes nm e
      T.EApp e1 e2  -> getVarTypes nm (e1,e2)
      T.EAbs x t e  -> getVarTypes nm e . Map.insert x (nm, T.tMono t)
      T.ELocated _ e -> getVarTypes nm e
      T.EProofAbs _ e -> getVarTypes nm e
      T.EProofApp e -> getVarTypes nm e
      T.EWhere e ds     -> getVarTypes nm (e,ds)
      T.EPropGuards gs _ -> getVarTypes nm (map snd gs)

instance GetVarTypes T.CaseAlt where
  getVarTypes nm (T.CaseAlt xs e) =
    getVarTypes nm e . flip (foldr (\(x,t) -> Map.insert x (nm, T.tMono t))) xs

instance GetVarTypes T.Match where
  getVarTypes nm m =
    case m of
      T.From x _ t e -> getVarTypes nm e . Map.insert x (nm, T.tMono t)
      T.Let d -> getVarTypes nm d

instance GetVarTypes T.NominalType where
  getVarTypes nm nom = flip (foldr (\(x,t) -> Map.insert x (nm1,t))) cons 
    where
    cons = T.nominalTypeConTypes nom
    nm1  = T.addTNames (T.ntParams nom) nm



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
      _ ->
        case curRange ctx of
          Nothing -> rest
          Just r  -> rest { ixUse = (r,a) : ixUse rest }

newtype Def = Def Name

instance RangedVars Def where
  rangedVars (Def a) ctx rest =
    case nameInfo a of
      GlobalName SystemName _ -> rest
      _ -> rest {
        ixDefs = Map.insert a info (ixDefs rest),
        ixUse = (r,a) : ixUse rest
      }
    where
    r = nameLoc a
    blankInfo = DefInfo {
      defName  = a,
      defRange = r,
      defDoc   = Nothing,
      defType  = Nothing   -- added later
    }
    info =
      case nameInfo a of 
        GlobalName {} -> blankInfo { defDoc = curDoc ctx }
        _             -> blankInfo
    

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
      TDNewtype nt -> rangedVars nt
      TDEnum en -> rangedVars en
      DInterfaceConstraint _ xs -> rangedVars xs
      _ -> const id -- XXX
      
      {-
  
  
  | DParamDecl Range (Signature name)   -- ^ @parameter ...@ (parser only)

  | DModule (TopLevel (NestedModule name))      -- ^ @submodule M where ...@
  | DImport (Located (ImportG (ImpName name)))  -- ^ @import X@
  | DModParam (ModParam name)                   -- ^ @import interface X ...@
  
-}

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
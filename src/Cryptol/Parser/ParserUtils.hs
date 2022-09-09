-- |
-- Module      :  Cryptol.Parser.ParserUtils
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.Parser.ParserUtils where

import Data.Maybe(fromMaybe)
import Data.Bits(testBit,setBit)
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import Control.Monad(liftM,ap,unless,guard)
import qualified Control.Monad.Fail as Fail
import           Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Map as Map
import Text.Read(readMaybe)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat


import Cryptol.Parser.AST
import Cryptol.Parser.Lexer
import Cryptol.Parser.Token(SelectorType(..))
import Cryptol.Parser.Position
import Cryptol.Parser.Utils (translateExprToNumT,widthIdent)
import Cryptol.Utils.Ident(packModName,packIdent,modNameChunks)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic
import Cryptol.Utils.RecordMap


parseString :: Config -> ParseM a -> String -> Either ParseError a
parseString cfg p cs = parse cfg p (T.pack cs)

parse :: Config -> ParseM a -> Text -> Either ParseError a
parse cfg p cs    = case unP p cfg eofPos S { sPrevTok = Nothing
                                            , sTokens = toks
                                            , sNextTyParamNum = 0
                                            } of
                      Left err    -> Left err
                      Right (a,_) -> Right a
  where (toks,eofPos) = lexer cfg cs


{- The parser is parameterized by the pozition of the final token. -}
newtype ParseM a =
  P { unP :: Config -> Position -> S -> Either ParseError (a,S) }


lexerP :: (Located Token -> ParseM a) -> ParseM a
lexerP k = P $ \cfg p s ->
  case sTokens s of
    t : _ | Err e <- tokenType it ->
      Left $ HappyErrorMsg (srcRange t) $
        [case e of
           UnterminatedComment -> "unterminated comment"
           UnterminatedString  -> "unterminated string"
           UnterminatedChar    -> "unterminated character"
           InvalidString       -> "invalid string literal: " ++
                                    T.unpack (tokenText it)
           InvalidChar         -> "invalid character literal: " ++
                                    T.unpack (tokenText it)
           LexicalError        -> "unrecognized character: " ++
                                    T.unpack (tokenText it)
           MalformedLiteral    -> "malformed literal: " ++
                                    T.unpack (tokenText it)
           MalformedSelector   -> "malformed selector: " ++
                                    T.unpack (tokenText it)
           InvalidIndentation c -> "invalid indentation, unmatched " ++
              case c of
                Sym CurlyR    -> "{ ... } "
                Sym ParenR    -> "( ... )"
                Sym BracketR  -> "[ ... ]"
                _             -> show c -- basically panic
        ]
      where it = thing t

    t : more -> unP (k t) cfg p s { sPrevTok = Just t, sTokens = more }
    [] -> Left (HappyOutOfTokens (cfgSource cfg) p)

data ParseError = HappyError FilePath         {- Name of source file -}
                             (Located Token)  {- Offending token -}
                | HappyErrorMsg Range [String]
                | HappyUnexpected FilePath (Maybe (Located Token)) String
                | HappyOutOfTokens FilePath Position
                  deriving (Show, Generic, NFData)

data S = S { sPrevTok :: Maybe (Located Token)
           , sTokens :: [Located Token]
           , sNextTyParamNum :: !Int
             -- ^ Keep track of the type parameters as they appear in the input
           }

ppError :: ParseError -> Doc

ppError (HappyError path ltok)
  | Err _ <- tokenType tok =
    text "Parse error at" <+>
    text path <.> char ':' <.> pp pos <.> comma <+>
    pp tok

  | White DocStr <- tokenType tok =
    "Unexpected documentation (/**) comment at" <+>
    text path <.> char ':' <.> pp pos <.> colon $$
    indent 2
      "Documentation comments need to be followed by something to document."

  | otherwise =
    text "Parse error at" <+>
    text path <.> char ':' <.> pp pos <.> comma $$
    indent 2 (text "unexpected:" <+> pp tok)
  where
  pos = from (srcRange ltok)
  tok = thing ltok

ppError (HappyOutOfTokens path pos) =
  text "Unexpected end of file at:" <+>
    text path <.> char ':' <.> pp pos

ppError (HappyErrorMsg p xs)  = text "Parse error at" <+> pp p $$ indent 2 (vcat (map text xs))

ppError (HappyUnexpected path ltok e) =
  nest 2 $ vcat $
   [ text "Parse error at" <+> text path <.> char ':' <.> pp pos <.> comma ]
   ++ unexp
   ++ ["expected:" <+> text e]
  where
  (unexp,pos) =
    case ltok of
      Nothing -> ( [] ,start)
      Just t  -> ( ["unexpected:" <+> text (T.unpack (tokenText (thing t)))]
                 , from (srcRange t)
                 )

instance Functor ParseM where
  fmap = liftM

instance Applicative ParseM where
  pure a = P (\_ _ s -> Right (a,s))
  (<*>) = ap

instance Monad ParseM where
  return    = pure
  m >>= k   = P (\cfg p s1 -> case unP m cfg p s1 of
                            Left e       -> Left e
                            Right (a,s2) -> unP (k a) cfg p s2)

instance Fail.MonadFail ParseM where
  fail s    = panic "[Parser] fail" [s]

happyError :: ParseM a
happyError = P $ \cfg _ s ->
  case sPrevTok s of
    Just t  -> Left (HappyError (cfgSource cfg) t)
    Nothing ->
      Left (HappyErrorMsg emptyRange ["Parse error at the beginning of the file"])

errorMessage :: Range -> [String] -> ParseM a
errorMessage r xs = P $ \_ _ _ -> Left (HappyErrorMsg r xs)

customError :: String -> Located Token -> ParseM a
customError x t = P $ \_ _ _ -> Left (HappyErrorMsg (srcRange t) [x])

expected :: String -> ParseM a
expected x = P $ \cfg _ s ->
                    Left (HappyUnexpected (cfgSource cfg) (sPrevTok s) x)









mkModName :: [Text] -> ModName
mkModName = packModName

-- Note that type variables are not resolved at this point: they are tcons.
mkSchema :: [TParam PName] -> [Prop PName] -> Type PName -> Schema PName
mkSchema xs ps t = Forall xs ps t Nothing

getName :: Located Token -> PName
getName l = case thing l of
              Token (Ident [] x) _ -> mkUnqual (mkIdent x)
              _ -> panic "[Parser] getName" ["not an Ident:", show l]

getNum :: Located Token -> Integer
getNum l = case thing l of
             Token (Num x _ _) _ -> x
             Token (ChrLit x) _  -> toInteger (fromEnum x)
             _ -> panic "[Parser] getNum" ["not a number:", show l]

getChr :: Located Token -> Char
getChr l = case thing l of
             Token (ChrLit x) _  -> x
             _ -> panic "[Parser] getChr" ["not a char:", show l]

getStr :: Located Token -> String
getStr l = case thing l of
             Token (StrLit x) _ -> x
             _ -> panic "[Parser] getStr" ["not a string:", show l]

numLit :: Token -> Expr PName
numLit Token { tokenText = txt, tokenType = Num x base digs }
  | base == 2   = ELit $ ECNum x (BinLit txt digs)
  | base == 8   = ELit $ ECNum x (OctLit txt digs)
  | base == 10  = ELit $ ECNum x (DecLit txt)
  | base == 16  = ELit $ ECNum x (HexLit txt digs)

numLit x = panic "[Parser] numLit" ["invalid numeric literal", show x]

fracLit :: Token -> Expr PName
fracLit tok =
  case tokenType tok of
    Frac x base
      | base == 2   -> ELit $ ECFrac x $ BinFrac $ tokenText tok
      | base == 8   -> ELit $ ECFrac x $ OctFrac $ tokenText tok
      | base == 10  -> ELit $ ECFrac x $ DecFrac $ tokenText tok
      | base == 16  -> ELit $ ECFrac x $ HexFrac $ tokenText tok
    _ -> panic "[Parser] fracLit" [ "Invalid fraction", show tok ]


intVal :: Located Token -> ParseM Integer
intVal tok =
  case tokenType (thing tok) of
    Num x _ _ -> return x
    _         -> errorMessage (srcRange tok) ["Expected an integer"]

mkFixity :: Assoc -> Located Token -> [LPName] -> ParseM (Decl PName)
mkFixity assoc tok qns =
  do l <- intVal tok
     unless (l >= 1 && l <= 100)
          (errorMessage (srcRange tok) ["Fixity levels must be between 1 and 100"])
     return (DFixity (Fixity assoc (fromInteger l)) qns)

fromStrLit :: Located Token -> ParseM (Located String)
fromStrLit loc = case tokenType (thing loc) of
  StrLit str -> return loc { thing = str }
  _          -> errorMessage (srcRange loc) ["Expected a string literal"]


validDemotedType :: Range -> Type PName -> ParseM (Type PName)
validDemotedType rng ty =
  case ty of
    TLocated t r -> validDemotedType r t
    TRecord {}   -> bad "Record types"
    TTyApp {}    -> bad "Explicit type application"
    TTuple {}    -> bad "Tuple types"
    TFun {}      -> bad "Function types"
    TSeq {}      -> bad "Sequence types"
    TBit         -> bad "Type bit"
    TNum {}      -> ok
    TChar {}     -> ok
    TWild        -> bad "Wildcard types"
    TUser {}     -> ok

    TParens t    -> validDemotedType rng t
    TInfix{}     -> ok

  where bad x = errorMessage rng [x ++ " cannot be demoted."]
        ok    = return $ at rng ty

-- | Input fields are reversed!
mkRecord :: AddLoc b => Range -> (RecordMap Ident (Range, a) -> b) -> [Named a] -> ParseM b
mkRecord rng f xs =
   case res of
     Left (nm,(nmRng,_)) -> errorMessage nmRng ["Record has repeated field: " ++ show (pp nm)]
     Right r -> pure $ at rng (f r)

  where
  res = recordFromFieldsErr ys
  ys = map (\ (Named (Located r nm) x) -> (nm,(r,x))) (reverse xs)


-- | Input expression are reversed
mkEApp :: NonEmpty (Expr PName) -> ParseM (Expr PName)

mkEApp es@(eLast :| _) =
    do f :| xs <- cvtTypeParams eFirst rest
       pure (at (eFirst,eLast) $ foldl EApp f xs)

  where
  eFirst :| rest = NE.reverse es

  {- Type applications are parsed as `ETypeVal (TTyApp fs)` expressions.
     Here we associate them with their corresponding functions,
     converting them into `EAppT` constructs.  For example:

     [ f, x, `{ a = 2 }, y ]
     becomes
     [ f, x ` { a = 2 }, y ]

     The parser associates field and tuple projectors that follow an
     explicit type application onto the TTyApp term, so we also
     have to unwind those projections and reapply them.  For example:

     [ f, x, `{ a = 2 }.f.2, y ]
     becomes
     [ f, (x`{ a = 2 }).f.2, y ]

  -}
  cvtTypeParams e [] = pure (e :| [])
  cvtTypeParams e (p : ps) =
    case toTypeParam p Nothing of
      Nothing -> NE.cons e <$> cvtTypeParams p ps

      Just (fs,ss,rng) ->
        if checkAppExpr e then
          let e'  = foldr (flip ESel) (EAppT e fs) ss
              e'' = case rCombMaybe (getLoc e) rng of
                      Just r -> ELocated e' r
                      Nothing -> e'
           in cvtTypeParams e'' ps
        else
          errorMessage (fromMaybe emptyRange (getLoc e))
                  [ "Explicit type applications can only be applied to named values."
                  , "Unexpected: " ++ show (pp e)
                  ]

  {- Check if the given expression is a legal target for explicit type application.
     This is basically only variables, but we also allow the parenthesis and
     the phantom "located" AST node.
   -}
  checkAppExpr e =
    case e of
      ELocated e' _ -> checkAppExpr e'
      EParens e'    -> checkAppExpr e'
      EVar{}        -> True
      _             -> False

  {- Look under a potential chain of selectors to see if we have a TTyApp.
     If so, return the ty app information and the collected selectors
     to reapply.
   -}
  toTypeParam e mr =
    case e of
      ELocated e' rng -> toTypeParam e' (rCombMaybe mr (Just rng))
      ETypeVal t -> toTypeParam' t mr
      ESel e' s  -> ( \(fs,ss,r) -> (fs,s:ss,r) ) <$> toTypeParam e' mr
      _          ->  Nothing

  toTypeParam' t mr =
    case t of
      TLocated t' rng -> toTypeParam' t' (rCombMaybe mr (Just rng))
      TTyApp fs -> Just (map mkTypeInst fs, [], mr)
      _ -> Nothing

unOp :: Expr PName -> Expr PName -> Expr PName
unOp f x = at (f,x) $ EApp f x

-- Use defaultFixity as a placeholder, it will be fixed during renaming.
binOp :: Expr PName -> Located PName -> Expr PName -> Expr PName
binOp x f y = at (x,y) $ EInfix x f defaultFixity y

-- An element type ascription is allowed to appear on one of the arguments.
eFromTo :: Range -> Expr PName -> Maybe (Expr PName) -> Expr PName -> ParseM (Expr PName)
eFromTo r e1 e2 e3 =
  case (asETyped e1, asETyped =<< e2, asETyped e3) of
    (Just (e1', t), Nothing, Nothing) -> eFromToType r e1' e2 e3 (Just t)
    (Nothing, Just (e2', t), Nothing) -> eFromToType r e1 (Just e2') e3 (Just t)
    (Nothing, Nothing, Just (e3', t)) -> eFromToType r e1 e2 e3' (Just t)
    (Nothing, Nothing, Nothing) -> eFromToType r e1 e2 e3 Nothing
    _ -> errorMessage r ["A sequence enumeration may have at most one element type annotation."]

eFromToBy :: Range -> Expr PName -> Expr PName -> Expr PName -> Bool -> ParseM (Expr PName)
eFromToBy r e1 e2 e3 isStrictBound =
  case (asETyped e1, asETyped e2, asETyped e3) of
    (Just (e1', t), Nothing, Nothing) -> eFromToByTyped r e1' e2 e3 (Just t) isStrictBound
    (Nothing, Just (e2', t), Nothing) -> eFromToByTyped r e1 e2' e3 (Just t) isStrictBound
    (Nothing, Nothing, Just (e3', t)) -> eFromToByTyped r e1 e2 e3' (Just t) isStrictBound
    (Nothing, Nothing, Nothing)       -> eFromToByTyped r e1 e2 e3 Nothing isStrictBound
    _ -> errorMessage r ["A sequence enumeration may have at most one element type annotation."]

eFromToByTyped :: Range -> Expr PName -> Expr PName -> Expr PName -> Maybe (Type PName) -> Bool -> ParseM (Expr PName)
eFromToByTyped r e1 e2 e3 t isStrictBound =
  EFromToBy isStrictBound
      <$> exprToNumT r e1
      <*> exprToNumT r e2
      <*> exprToNumT r e3
      <*> pure t

eFromToDownBy ::
  Range -> Expr PName -> Expr PName -> Expr PName -> Bool -> ParseM (Expr PName)
eFromToDownBy r e1 e2 e3 isStrictBound =
  case (asETyped e1, asETyped e2, asETyped e3) of
    (Just (e1', t), Nothing, Nothing) -> eFromToDownByTyped r e1' e2 e3 (Just t) isStrictBound
    (Nothing, Just (e2', t), Nothing) -> eFromToDownByTyped r e1 e2' e3 (Just t) isStrictBound
    (Nothing, Nothing, Just (e3', t)) -> eFromToDownByTyped r e1 e2 e3' (Just t) isStrictBound
    (Nothing, Nothing, Nothing)       -> eFromToDownByTyped r e1 e2 e3 Nothing isStrictBound
    _ -> errorMessage r ["A sequence enumeration may have at most one element type annotation."]

eFromToDownByTyped ::
  Range -> Expr PName -> Expr PName -> Expr PName -> Maybe (Type PName) -> Bool -> ParseM (Expr PName)
eFromToDownByTyped r e1 e2 e3 t isStrictBound =
  EFromToDownBy isStrictBound
      <$> exprToNumT r e1
      <*> exprToNumT r e2
      <*> exprToNumT r e3
      <*> pure t


asETyped :: Expr n -> Maybe (Expr n, Type n)
asETyped (ELocated e _) = asETyped e
asETyped (ETyped e t) = Just (e, t)
asETyped _ = Nothing

eFromToType ::
  Range -> Expr PName -> Maybe (Expr PName) -> Expr PName -> Maybe (Type PName) -> ParseM (Expr PName)
eFromToType r e1 e2 e3 t =
  EFromTo <$> exprToNumT r e1
          <*> mapM (exprToNumT r) e2
          <*> exprToNumT r e3
          <*> pure t

eFromToLessThan ::
  Range -> Expr PName -> Expr PName -> ParseM (Expr PName)
eFromToLessThan r e1 e2 =
  case asETyped e2 of
    Just _  -> errorMessage r ["The exclusive upper bound of an enumeration may not have a type annotation."]
    Nothing ->
      case asETyped e1 of
        Nothing      -> eFromToLessThanType r e1  e2 Nothing
        Just (e1',t) -> eFromToLessThanType r e1' e2 (Just t)

eFromToLessThanType ::
  Range -> Expr PName -> Expr PName -> Maybe (Type PName) -> ParseM (Expr PName)
eFromToLessThanType r e1 e2 t =
  EFromToLessThan
    <$> exprToNumT r e1
    <*> exprToNumT r e2
    <*> pure t

exprToNumT :: Range -> Expr PName -> ParseM (Type PName)
exprToNumT r expr =
  case translateExprToNumT expr of
    Just t -> return t
    Nothing -> bad
  where
  bad = errorMessage (fromMaybe r (getLoc expr))
        [ "The boundaries of .. sequences should be valid numeric types."
        , "The expression `" ++ show (pp expr) ++ "` is not."
        ]


-- | WARNING: This is a bit of a hack.
-- It is used to represent anonymous type applications.
anonTyApp :: Maybe Range -> [Type PName] -> Type PName
anonTyApp ~(Just r) ts = TLocated (TTyApp (map toField ts)) r
  where noName    = Located { srcRange = r, thing = mkIdent (T.pack "") }
        toField t = Named { name = noName, value = t }

exportDecl :: Maybe (Located Text) -> ExportType -> Decl PName -> TopDecl PName
exportDecl mbDoc e d = Decl TopLevel { tlExport = e
                                     , tlDoc    = mbDoc
                                     , tlValue  = d }

exportNewtype :: ExportType -> Maybe (Located Text) -> Newtype PName ->
                                                            TopDecl PName
exportNewtype e d n = TDNewtype TopLevel { tlExport = e
                                         , tlDoc    = d
                                         , tlValue  = n }

exportModule :: Maybe (Located Text) -> NestedModule PName -> TopDecl PName
exportModule mbDoc m = DModule TopLevel { tlExport = Public
                                        , tlDoc    = mbDoc
                                        , tlValue  = m }

mkParFun :: Maybe (Located Text) ->
            Located PName ->
            Schema PName ->
            TopDecl PName
mkParFun mbDoc n s = DParameterFun ParameterFun { pfName = n
                                                , pfSchema = s
                                                , pfDoc = thing <$> mbDoc
                                                , pfFixity = Nothing
                                                }

mkParType :: Maybe (Located Text) ->
             Located PName ->
             Located Kind ->
             ParseM (TopDecl PName)
mkParType mbDoc n k =
  do num <- P $ \_ _ s -> let nu = sNextTyParamNum s
                          in Right (nu, s { sNextTyParamNum = nu + 1 })
     return (DParameterType
             ParameterType { ptName    = n
                           , ptKind    = thing k
                           , ptDoc     = thing <$> mbDoc
                           , ptFixity  = Nothing
                           , ptNumber  = num
                           })

changeExport :: ExportType -> [TopDecl PName] -> [TopDecl PName]
changeExport e = map change
  where
  change (Decl d)      = Decl      d { tlExport = e }
  change (DPrimType t) = DPrimType t { tlExport = e }
  change (TDNewtype n) = TDNewtype n { tlExport = e }
  change (DModule m)   = DModule   m { tlExport = e }
  change td@Include{}  = td
  change td@DImport{}  = td
  change (DParameterType {}) = panic "changeExport" ["private type parameter?"]
  change (DParameterFun {})  = panic "changeExport" ["private value parameter?"]
  change (DParameterConstraint {}) =
    panic "changeExport" ["private type constraint parameter?"]

mkTypeInst :: Named (Type PName) -> TypeInst PName
mkTypeInst x | nullIdent (thing (name x)) = PosInst (value x)
             | otherwise                  = NamedInst x


mkTParam :: Located Ident -> Maybe Kind -> ParseM (TParam PName)
mkTParam Located { srcRange = rng, thing = n } k
  | n == widthIdent = errorMessage rng ["`width` is not a valid type parameter name."]
  | otherwise       = return (TParam (mkUnqual n) k (Just rng))

mkTySyn :: Located PName -> [TParam PName] -> Type PName -> ParseM (Decl PName)
mkTySyn ln ps b
  | getIdent (thing ln) == widthIdent =
    errorMessage (srcRange ln) ["`width` is not a valid type synonym name."]

  | otherwise =
    return $ DType $ TySyn ln Nothing ps b

mkPropSyn :: Located PName -> [TParam PName] -> Type PName -> ParseM (Decl PName)
mkPropSyn ln ps b
  | getIdent (thing ln) == widthIdent =
    errorMessage (srcRange ln) ["`width` is not a valid constraint synonym name."]

  | otherwise =
    DProp . PropSyn ln Nothing ps . thing <$> mkProp b

polyTerm :: Range -> Integer -> Integer -> ParseM (Bool, Integer)
polyTerm rng k p
  | k == 0          = return (False, p)
  | k == 1          = return (True, p)
  | otherwise       = errorMessage rng ["Invalid polynomial coefficient"]

mkPoly :: Range -> [ (Bool,Integer) ] -> ParseM (Expr PName)
mkPoly rng terms
  | w <= toInteger (maxBound :: Int) = mk 0 (map fromInteger bits)
  | otherwise = errorMessage rng ["Polynomial literal too large: " ++ show w]

  where
  w    = case terms of
           [] -> 0
           _  -> 1 + maximum (map snd terms)

  bits = [ n | (True,n) <- terms ]

  mk :: Integer -> [Int] -> ParseM (Expr PName)
  mk res [] = return $ ELit $ ECNum res (PolyLit (fromInteger w :: Int))

  mk res (n : ns)
    | testBit res n = errorMessage rng
                       ["Polynomial contains multiple terms with exponent " ++ show n]
    | otherwise     = mk (setBit res n) ns


-- NOTE: The list of patterns is reversed!
mkProperty :: LPName -> [Pattern PName] -> Expr PName -> Decl PName
mkProperty f ps e = at (f,e) $
                    DBind Bind { bName       = f
                               , bParams     = reverse ps
                               , bDef        = at e (Located emptyRange (DExpr e))
                               , bSignature  = Nothing
                               , bPragmas    = [PragmaProperty]
                               , bMono       = False
                               , bInfix      = False
                               , bFixity     = Nothing
                               , bDoc        = Nothing
                               , bExport     = Public
                               }

-- NOTE: The lists of patterns are reversed!
mkIndexedDecl ::
  LPName -> ([Pattern PName], [Pattern PName]) -> Expr PName -> Decl PName
mkIndexedDecl f (ps, ixs) e =
  DBind Bind { bName       = f
             , bParams     = reverse ps
             , bDef        = at e (Located emptyRange (DExpr rhs))
             , bSignature  = Nothing
             , bPragmas    = []
             , bMono       = False
             , bInfix      = False
             , bFixity     = Nothing
             , bDoc        = Nothing
             , bExport     = Public
             }
  where
    rhs :: Expr PName
    rhs = mkGenerate (reverse ixs) e

-- NOTE: The lists of patterns are reversed!
mkIndexedExpr :: ([Pattern PName], [Pattern PName]) -> Expr PName -> Expr PName
mkIndexedExpr (ps, ixs) body
  | null ps = mkGenerate (reverse ixs) body
  | otherwise = EFun emptyFunDesc (reverse ps) (mkGenerate (reverse ixs) body)

mkGenerate :: [Pattern PName] -> Expr PName -> Expr PName
mkGenerate pats body =
  foldr (\pat e -> EGenerate (EFun emptyFunDesc [pat] e)) body pats

mkIf :: [(Expr PName, Expr PName)] -> Expr PName -> Expr PName
mkIf ifThens theElse = foldr addIfThen theElse ifThens
    where
    addIfThen (cond, doexpr) elseExpr = EIf cond doexpr elseExpr

mkPrimDecl :: Maybe (Located Text) -> LPName -> Schema PName -> [TopDecl PName]
mkPrimDecl = mkNoImplDecl DPrim

mkForeignDecl :: Maybe (Located Text) -> LPName -> Schema PName -> [TopDecl PName]
mkForeignDecl = mkNoImplDecl DForeign

-- | Generate a signature and a binding for value declarations with no
-- implementation (i.e. primitive or foreign declarations).  The reason for
-- generating both instead of just adding the signature at this point is that it
-- means the declarations don't need to be treated differently in the noPat
-- pass.  This is also the reason we add the doc to the TopLevel constructor,
-- instead of just place it on the binding directly.  A better solution might be
-- to just have a different constructor for primitives and foreigns.
mkNoImplDecl :: BindDef PName
  -> Maybe (Located Text) -> LPName -> Schema PName -> [TopDecl PName]
mkNoImplDecl def mbDoc ln sig =
  [ exportDecl mbDoc Public
    $ DBind Bind { bName      = ln
                 , bParams    = []
                 , bDef       = at sig (Located emptyRange def)
                 , bSignature = Nothing
                 , bPragmas   = []
                 , bMono      = False
                 , bInfix     = isInfixIdent (getIdent (thing ln))
                 , bFixity    = Nothing
                 , bDoc       = Nothing
                 , bExport    = Public
                 }
  , exportDecl Nothing Public
    $ DSignature [ln] sig
  ]

mkPrimTypeDecl ::
  Maybe (Located Text) ->
  Schema PName ->
  Located Kind ->
  ParseM [TopDecl PName]
mkPrimTypeDecl mbDoc (Forall as qs st ~(Just schema_rng)) finK =
  case splitT schema_rng st of
    Just (n,xs) ->
      do vs <- mapM tpK as
         unless (distinct (map fst vs)) $
            errorMessage schema_rng ["Repeated parameters."]
         let kindMap = Map.fromList vs
             lkp v = case Map.lookup (thing v) kindMap of
                       Just (k,tp)  -> pure (k,tp)
                       Nothing ->
                        errorMessage
                            (srcRange v)
                            ["Undefined parameter: " ++ show (pp (thing v))]
         (as',ins) <- unzip <$> mapM lkp xs
         unless (length vs == length xs) $
           errorMessage schema_rng ["All parameters should appear in the type."]

         let ki = finK { thing = foldr KFun (thing finK) ins }

         pure [ DPrimType TopLevel
                  { tlExport = Public
                  , tlDoc    = mbDoc
                  , tlValue  = PrimType { primTName   = n
                                        , primTKind   = ki
                                        , primTCts    = (as',qs)
                                        , primTFixity = Nothing
                                        }
                 }
              ]

    Nothing -> errorMessage schema_rng ["Invalid primitive signature"]

  where
  splitT r ty = case ty of
                  TLocated t r1 -> splitT r1 t
                  TUser n ts -> mkT r Located { srcRange = r, thing = n } ts
                  TInfix t1 n _ t2  -> mkT r n [t1,t2]
                  _ -> Nothing

  mkT r n ts = do ts1 <- mapM (isVar r) ts
                  guard (distinct (map thing ts1))
                  pure (n,ts1)

  isVar r ty = case ty of
                 TLocated t r1  -> isVar r1 t
                 TUser n []     -> Just Located { srcRange = r, thing = n }
                 _              -> Nothing

  -- inefficient, but the lists should be small
  distinct xs = case xs of
                  [] -> True
                  x : ys -> not (x `elem` ys) && distinct ys

  tpK tp = case tpKind tp of
             Just k  -> pure (tpName tp, (tp,k))
             Nothing ->
              case tpRange tp of
                Just r -> errorMessage r ["Parameters need a kind annotation"]
                Nothing -> panic "mkPrimTypeDecl"
                              [ "Missing range on schema parameter." ]


-- | Fix-up the documentation strings by removing the comment delimiters on each
-- end, and stripping out common prefixes on all the remaining lines.
mkDoc :: Located Text -> Located Text
mkDoc ltxt = ltxt { thing = docStr }
  where

  docStr = T.unlines
         $ dropPrefix
         $ trimFront
         $ T.lines
         $ T.dropWhileEnd commentChar
         $ thing ltxt

  commentChar :: Char -> Bool
  commentChar x = x `elem` ("/* \r\n\t" :: String)

  prefixDroppable x = x `elem` ("* \r\n\t" :: String)

  whitespaceChar :: Char -> Bool
  whitespaceChar x = x `elem` (" \r\n\t" :: String)

  trimFront []                     = []
  trimFront (l:ls)
    | T.all commentChar l = ls
    | otherwise           = T.dropWhile commentChar l : ls

  dropPrefix []        = []
  dropPrefix [t]       = [T.dropWhile commentChar t]
  dropPrefix ts@(l:ls) =
    case T.uncons l of
      Just (c,_) | prefixDroppable c &&
                   all (commonPrefix c) ls -> dropPrefix (map (T.drop 1) ts)
      _                                    -> ts

    where
    commonPrefix c t =
      case T.uncons t of
        Just (c',_) -> c == c'
        Nothing     -> whitespaceChar c -- end-of-line matches any whitespace


distrLoc :: Located [a] -> [Located a]
distrLoc x = [ Located { srcRange = r, thing = a } | a <- thing x ]
  where r = srcRange x


mkProp :: Type PName -> ParseM (Located [Prop PName])
mkProp ty =
  case ty of
    TLocated t r -> Located r `fmap` props r t
    _            -> panic "Parser" [ "Invalid type given to mkProp"
                                   , "expected a location"
                                   , show ty ]

  where

  props r t =
    case t of
      TInfix{}       -> return [CType t]
      TUser{}        -> return [CType t]
      TTuple ts      -> concat `fmap` mapM (props r) ts
      TParens t'     -> props r  t'
      TLocated t' r' -> props r' t'

      TFun{}    -> err
      TSeq{}    -> err
      TBit{}    -> err
      TNum{}    -> err
      TChar{}   -> err
      TWild     -> err
      TRecord{} -> err
      TTyApp{}  -> err

    where
    err = errorMessage r ["Invalid constraint"]

-- | Make an ordinary module
mkModule :: Located ModName -> [TopDecl PName] -> Module PName
mkModule nm ds = Module { mName = nm
                        , mInstance = Nothing
                        , mDecls = ds
                        }

mkNested :: Module PName -> ParseM (NestedModule PName)
mkNested m =
  case modNameChunks (thing nm) of
    [c] -> pure (NestedModule m { mName = nm { thing = mkUnqual (packIdent c)}})
    _   -> errorMessage r
                ["Nested modules names should be a simple identifier."]
  where
  nm = mName m
  r = srcRange nm

-- | Make an unnamed module---gets the name @Main@.
mkAnonymousModule :: [TopDecl PName] -> Module PName
mkAnonymousModule = mkModule Located { srcRange = emptyRange
                                     , thing    = mkModName [T.pack "Main"]
                                     }

-- | Make a module which defines a functor instance.
mkModuleInstance :: Located ModName ->
                    Located ModName ->
                    [TopDecl PName] ->
                    Module PName
mkModuleInstance nm fun ds =
  Module { mName     = nm
         , mInstance = Just fun
         , mDecls    = ds
         }

ufToNamed :: UpdField PName -> ParseM (Named (Expr PName))
ufToNamed (UpdField h ls e) =
  case (h,ls) of
    (UpdSet, [l]) | RecordSel i Nothing <- thing l ->
      pure Named { name = l { thing = i }, value = e }
    _ -> errorMessage (srcRange (head ls))
            ["Invalid record field.  Perhaps you meant to update a record?"]

exprToFieldPath :: Expr PName -> ParseM [Located Selector]
exprToFieldPath e0 = reverse <$> go noLoc e0
  where
  noLoc = panic "selExprToSels" ["Missing location?"]
  go loc expr =
    case expr of
      ELocated e1 r -> go r e1
      ESel e2 s ->
        do ls <- go loc e2
           let rng = loc { from = to (srcRange (head ls)) }
           pure (Located { thing = s, srcRange = rng } : ls)
      EVar (UnQual l) ->
        pure [ Located { thing = RecordSel l Nothing, srcRange = loc } ]

      ELit (ECNum n (DecLit {})) ->
        pure [ Located { thing = TupleSel (fromInteger n) Nothing
                       , srcRange = loc } ]

      ELit (ECFrac _ (DecFrac txt))
        | (as,bs') <- T.break (== '.') txt
        , Just a <- readMaybe (T.unpack as)
        , Just (_,bs) <- T.uncons bs'
        , Just b <- readMaybe (T.unpack bs)
        , let fromP = from loc
        , let midP  = fromP { col = col fromP + T.length as + 1 } ->
          -- these are backward because we reverse above
          pure [ Located { thing    = TupleSel b Nothing
                         , srcRange = loc { from = midP }
                         }
               , Located { thing    = TupleSel a Nothing
                         , srcRange = loc { to = midP }
                         }
               ]

      _ -> errorMessage loc ["Invalid label in record update."]


mkSelector :: Token -> Selector
mkSelector tok =
  case tokenType tok of
    Selector (TupleSelectorTok n) -> TupleSel n Nothing
    Selector (RecordSelectorTok t) -> RecordSel (mkIdent t) Nothing
    _ -> panic "mkSelector"
          [ "Unexpected selector token", show tok ]

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
module Cryptol.Parser.ParserUtils where

import Cryptol.Parser.AST
import Cryptol.Parser.Lexer
import Cryptol.Parser.Position
import Cryptol.Parser.Utils (translateExprToNumT,widthIdent)
import Cryptol.Utils.Ident(packModName)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic

import Data.Maybe(fromMaybe)
import Data.Bits(testBit,setBit)
import Control.Monad(liftM,ap,unless)
import           Data.Text(Text)
import qualified Data.Text as T


import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

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
         case e of
           UnterminatedComment -> "unterminated comment"
           UnterminatedString  -> "unterminated string"
           UnterminatedChar    -> "unterminated character"
           InvalidString       -> "invalid string literal:" ++
                                    T.unpack (tokenText it)
           InvalidChar         -> "invalid character literal:" ++
                                    T.unpack (tokenText it)
           LexicalError        -> "unrecognized character:" ++
                                    T.unpack (tokenText it)
      where it = thing t

    t : more -> unP (k t) cfg p s { sPrevTok = Just t, sTokens = more }
    [] -> Left (HappyOutOfTokens (cfgSource cfg) p)

data ParseError = HappyError FilePath         {- Name of source file -}
                             (Located Token)  {- Offending token -}
                | HappyErrorMsg Range String
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
    nest 2
      "Documentation comments need to be followed by something to document."

  | otherwise =
    text "Parse error at" <+>
    text path <.> char ':' <.> pp pos <.> comma $$
    nest 2 (text "unexpected:" <+> pp tok)
  where
  pos = from (srcRange ltok)
  tok = thing ltok

ppError (HappyOutOfTokens path pos) =
  text "Unexpected end of file at:" <+>
    text path <.> char ':' <.> pp pos

ppError (HappyErrorMsg p x)  = text "Parse error at" <+> pp p $$ nest 2 (text x)

ppError (HappyUnexpected path ltok e) =
  text "Parse error at" <+>
   text path <.> char ':' <.> pp pos <.> comma $$
   nest 2 unexp $$
   nest 2 ("expected:" <+> text e)
  where
  (unexp,pos) =
    case ltok of
      Nothing -> (empty,start)
      Just t  -> ( "unexpected:" <+> text (T.unpack (tokenText (thing t)))
                 , from (srcRange t)
                 )

instance Functor ParseM where
  fmap = liftM

instance Applicative ParseM where
  pure  = return
  (<*>) = ap

instance Monad ParseM where
  return a  = P (\_ _ s -> Right (a,s))
  fail s    = panic "[Parser] fail" [s]
  m >>= k   = P (\cfg p s1 -> case unP m cfg p s1 of
                            Left e       -> Left e
                            Right (a,s2) -> unP (k a) cfg p s2)

happyError :: ParseM a
happyError = P $ \cfg _ s ->
  case sPrevTok s of
    Just t  -> Left (HappyError (cfgSource cfg) t)
    Nothing ->
      Left (HappyErrorMsg emptyRange "Parse error at the beginning of the file")

errorMessage :: Range -> String -> ParseM a
errorMessage r x = P $ \_ _ _ -> Left (HappyErrorMsg r x)

customError :: String -> Located Token -> ParseM a
customError x t = P $ \_ _ _ -> Left (HappyErrorMsg (srcRange t) x)

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
             Token (ChrLit x) _  -> fromIntegral (fromEnum x)
             _ -> panic "[Parser] getNum" ["not a number:", show l]

getStr :: Located Token -> String
getStr l = case thing l of
             Token (StrLit x) _ -> x
             _ -> panic "[Parser] getStr" ["not a string:", show l]

numLit :: TokenT -> Expr PName
numLit (Num x base digs)
  | base == 2   = ELit $ ECNum x (BinLit digs)
  | base == 8   = ELit $ ECNum x (OctLit digs)
  | base == 10  = ELit $ ECNum x DecLit
  | base == 16  = ELit $ ECNum x (HexLit digs)

numLit x = panic "[Parser] numLit" ["invalid numeric literal", show x]

intVal :: Located Token -> ParseM Integer
intVal tok =
  case tokenType (thing tok) of
    Num x _ _ -> return x
    _         -> errorMessage (srcRange tok) "Expected an integer"

mkFixity :: Assoc -> Located Token -> [LPName] -> ParseM (Decl PName)
mkFixity assoc tok qns =
  do l <- intVal tok
     unless (l >= 1 && l <= 100)
          (errorMessage (srcRange tok) "Fixity levels must be between 1 and 100")
     return (DFixity (Fixity assoc (fromInteger l)) qns)

mkTupleSel :: Range -> Integer -> ParseM (Located Selector)
mkTupleSel pos n
  | n < 0 = errorMessage pos
             (show n ++ " is not a valid tuple selector (they start from 0).")
  | toInteger asInt /= n  = errorMessage pos "Tuple selector is too large."
  | otherwise             = return $ Located pos $ TupleSel asInt Nothing
  where asInt = fromInteger n

fromStrLit :: Located Token -> ParseM (Located String)
fromStrLit loc = case tokenType (thing loc) of
  StrLit str -> return loc { thing = str }
  _          -> errorMessage (srcRange loc) "Expected a string literal"


validDemotedType :: Range -> Type PName -> ParseM (Type PName)
validDemotedType rng ty =
  case ty of
    TLocated t r -> validDemotedType r t
    TRecord {}   -> bad "Record types"
    TTuple {}    -> bad "Tuple types"
    TFun {}      -> bad "Function types"
    TSeq {}      -> bad "Sequence types"
    TBit         -> bad "Type bit"
    TNum {}      -> ok
    TChar {}     -> ok
    TWild        -> bad "Wildcard types"
    TUser {}     -> ok
    TApp {}      -> ok

    TParens t    -> validDemotedType rng t
    TInfix{}     -> ok

  where bad x = errorMessage rng (x ++ " cannot be demoted.")
        ok    = return $ at rng ty

mkEApp :: [Expr PName] -> Expr PName
mkEApp es@(eLast : _) = at (eFirst,eLast) $ foldl EApp f xs
  where
  eFirst : rest = reverse es
  f : xs        = cvtTypeParams eFirst rest

  {- Type applications are parsed as `ETypeVal (TRecord fs)` expressions.
     Here we associate them with their corresponding functions,
     converting them into `EAppT` constructs.  For example:

     [ f, x, `{ a = 2 }, y ]
     becomes
     [ f, x ` { a = 2 }, y ]
  -}
  cvtTypeParams e [] = [e]
  cvtTypeParams e (p : ps) =
    case toTypeParam p of
      Just fs -> cvtTypeParams (EAppT e fs) ps
      Nothing -> e : cvtTypeParams p ps

  toTypeParam e =
    case dropLoc e of
      ETypeVal t -> case dropLoc t of
                      TRecord fs -> Just (map mkTypeInst fs)
                      _          -> Nothing
      _          ->  Nothing

mkEApp es        = panic "[Parser] mkEApp" ["Unexpected:", show es]


unOp :: Expr PName -> Expr PName -> Expr PName
unOp f x = at (f,x) $ EApp f x

-- Use defaultFixity as a placeholder, it will be fixed during renaming.
binOp :: Expr PName -> Located PName -> Expr PName -> Expr PName
binOp x f y = at (x,y) $ EInfix x f defaultFixity y

eFromTo :: Range -> Expr PName -> Maybe (Expr PName) -> Expr PName -> ParseM (Expr PName)
eFromTo r e1 e2 e3 = EFromTo <$> exprToNumT r e1
                             <*> mapM (exprToNumT r) e2
                             <*> exprToNumT r e3

exprToNumT :: Range -> Expr PName -> ParseM (Type PName)
exprToNumT r expr =
  case translateExprToNumT expr of
    Just t -> return t
    Nothing -> bad
  where
  bad = errorMessage (fromMaybe r (getLoc expr)) $ unlines
        [ "The boundaries of .. sequences should be valid numeric types."
        , "The expression `" ++ show (pp expr) ++ "` is not."
        , ""
        , "If you were trying to specify the width of the elements,"
        , "you may add a type annotation outside the sequence. For example:"
        , "   [ 1 .. 10 ] : [_][16]"
        ]


-- | WARNING: This is a bit of a hack.
-- It is used to represent anonymous type applications.
anonRecord :: Maybe Range -> [Type PName] -> Type PName
anonRecord ~(Just r) ts = TRecord (map toField ts)
  where noName    = Located { srcRange = r, thing = mkIdent (T.pack "") }
        toField t = Named { name = noName, value = t }

exportDecl :: Maybe (Located String) -> ExportType -> Decl PName -> TopDecl PName
exportDecl mbDoc e d = Decl TopLevel { tlExport = e
                                     , tlDoc    = mbDoc
                                     , tlValue  = d }

exportNewtype :: ExportType -> Maybe (Located String) -> Newtype PName ->
                                                            TopDecl PName
exportNewtype e d n = TDNewtype TopLevel { tlExport = e
                                         , tlDoc    = d
                                         , tlValue  = n }

mkParFun :: Maybe (Located String) ->
            Located PName ->
            Schema PName ->
            TopDecl PName
mkParFun mbDoc n s = DParameterFun ParameterFun { pfName = n
                                                , pfSchema = s
                                                , pfDoc = thing <$> mbDoc
                                                , pfFixity = Nothing
                                                }

mkParType :: Maybe (Located String) ->
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
  change (TDNewtype n) = TDNewtype n { tlExport = e }
  change td@Include{}  = td
  change (DParameterType {}) = panic "changeExport" ["private type parameter?"]
  change (DParameterFun {})  = panic "changeExport" ["private value parameter?"]
  change (DParameterConstraint {}) =
    panic "changeExport" ["private type constraint parameter?"]

mkTypeInst :: Named (Type PName) -> TypeInst PName
mkTypeInst x | nullIdent (thing (name x)) = PosInst (value x)
             | otherwise                  = NamedInst x


mkTParam :: Located Ident -> Maybe Kind -> ParseM (TParam PName)
mkTParam Located { srcRange = rng, thing = n } k
  | n == widthIdent = errorMessage rng "`width` is not a valid type parameter name."
  | otherwise       = return (TParam (mkUnqual n) k (Just rng))

mkTySyn :: Located PName -> [TParam PName] -> Type PName -> ParseM (Decl PName)
mkTySyn ln ps b
  | getIdent (thing ln) == widthIdent =
    errorMessage (srcRange ln) "`width` is not a valid type synonym name."

  | otherwise =
    return $ DType $ TySyn ln ps b

mkPropSyn :: Located PName -> [TParam PName] -> Type PName -> ParseM (Decl PName)
mkPropSyn ln ps b
  | getIdent (thing ln) == widthIdent =
    errorMessage (srcRange ln) "`width` is not a valid constraint synonym name."

  | otherwise =
    DProp . PropSyn ln ps . thing <$> mkProp b

polyTerm :: Range -> Integer -> Integer -> ParseM (Bool, Integer)
polyTerm rng k p
  | k == 0          = return (False, p)
  | k == 1          = return (True, p)
  | otherwise       = errorMessage rng "Invalid polynomial coefficient"

mkPoly :: Range -> [ (Bool,Integer) ] -> ParseM (Expr PName)
mkPoly rng terms = mk 0 (map fromInteger bits)
  where
  w    = case terms of
           [] -> 0
           _  -> 1 + maximum (map (fromInteger . snd) terms)
  bits = [ n | (True,n) <- terms ]

  mk res []         = return $ ELit $ ECNum res (PolyLit w)
  mk res (n : ns)
    | testBit res n = errorMessage rng
                       ("Polynomial contains multiple terms with exponent "
                                                                    ++ show n)
    | otherwise     = mk (setBit res n) ns


-- NOTE: The list of patterns is reversed!
mkProperty :: LPName -> [Pattern PName] -> Expr PName -> Decl PName
mkProperty f ps e = DBind Bind { bName       = f
                               , bParams     = reverse ps
                               , bDef        = at e (Located emptyRange (DExpr e))
                               , bSignature  = Nothing
                               , bPragmas    = [PragmaProperty]
                               , bMono       = False
                               , bInfix      = False
                               , bFixity     = Nothing
                               , bDoc        = Nothing
                               }

mkIf :: [(Expr PName, Expr PName)] -> Expr PName -> Expr PName
mkIf ifThens theElse = foldr addIfThen theElse ifThens
    where
    addIfThen (cond, doexpr) elseExpr = EIf cond doexpr elseExpr

-- | Generate a signature and a primitive binding.  The reason for generating
-- both instead of just adding the signature at this point is that it means the
-- primitive declarations don't need to be treated differently in the noPat
-- pass.  This is also the reason we add the doc to the TopLevel constructor,
-- instead of just place it on the binding directly.  A better solution might be
-- to just have a different constructor for primitives.
mkPrimDecl :: Maybe (Located String) -> LPName -> Schema PName -> [TopDecl PName]
mkPrimDecl mbDoc ln sig =
  [ exportDecl mbDoc Public
    $ DBind Bind { bName      = ln
                 , bParams    = []
                 , bDef       = at sig (Located emptyRange DPrim)
                 , bSignature = Nothing
                 , bPragmas   = []
                 , bMono      = False
                 , bInfix     = isInfixIdent (getIdent (thing ln))
                 , bFixity    = Nothing
                 , bDoc       = Nothing
                 }
  , exportDecl Nothing Public
    $ DSignature [ln] sig
  ]

-- | Fix-up the documentation strings by removing the comment delimiters on each
-- end, and stripping out common prefixes on all the remaining lines.
mkDoc :: Located Text -> Located String
mkDoc ltxt = ltxt { thing = docStr }
  where

  docStr = unlines
         $ map T.unpack
         $ dropPrefix
         $ trimFront
         $ T.lines
         $ T.dropWhileEnd commentChar
         $ thing ltxt

  commentChar :: Char -> Bool
  commentChar x = x `elem` ("/* \r\n\t" :: String)

  prefixDroppable x = x `elem` ("* \r\n\t" :: String)

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
        Nothing     -> False


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
      TInfix{}       -> infixProp t
      TUser f xs     -> prefixProp r f xs
      TTuple ts      -> concat `fmap` mapM (props r) ts
      TParens t'     -> props r  t'
      TLocated t' r' -> props r' t'

      TApp{}    -> err
      TFun{}    -> err
      TSeq{}    -> err
      TBit{}    -> err
      TNum{}    -> err
      TChar{}   -> err
      TWild     -> err
      TRecord{} -> err

    where
    err = errorMessage r "Invalid constraint"

  -- we have to delay these until renaming, when we have the fixity table
  -- present
  infixProp t = return [CType t]

  -- these can be translated right away
  prefixProp r f xs
    | i == zeroIdent,      [x] <- xs = return [CLocated (CZero x) r]
    | i == logicIdent,     [x] <- xs = return [CLocated (CLogic x) r]
    | i == arithIdent,     [x] <- xs = return [CLocated (CArith x) r]
    | i == finIdent,       [x] <- xs = return [CLocated (CFin x) r]
    | i == cmpIdent,       [x] <- xs = return [CLocated (CCmp x) r]
    | i == signedCmpIdent, [x] <- xs = return [CLocated (CSignedCmp x) r]
    | i == literalIdent, [x,y] <- xs = return [CLocated (CLiteral x y) r]
    | otherwise                      = return [CLocated (CType (TUser f xs)) r]
    where
    i = getIdent f

zeroIdent, logicIdent, arithIdent, finIdent, cmpIdent, signedCmpIdent, literalIdent :: Ident
zeroIdent      = mkIdent "Zero"
logicIdent     = mkIdent "Logic"
arithIdent     = mkIdent "Arith"
finIdent       = mkIdent "fin"
cmpIdent       = mkIdent "Cmp"
signedCmpIdent = mkIdent "SignedCmp"
literalIdent   = mkIdent "Literal"

-- | Make an ordinary module
mkModule :: Located ModName ->
            ([Located Import], [TopDecl PName]) ->
            Module PName
mkModule nm (is,ds) = Module { mName = nm
                             , mInstance = Nothing
                             , mImports = is
                             , mDecls = ds
                             }

-- | Make an unnamed module---gets the name @Main@.
mkAnonymousModule :: ([Located Import], [TopDecl PName]) ->
                     Module PName
mkAnonymousModule = mkModule Located { srcRange = emptyRange
                                     , thing    = mkModName [T.pack "Main"]
                                     }

-- | Make a module which defines a functor instance.
mkModuleInstance :: Located ModName ->
                    Located ModName ->
                    ([Located Import], [TopDecl PName]) ->
                    Module PName
mkModuleInstance nm fun (is,ds) =
  Module { mName     = nm
         , mInstance = Just fun
         , mImports  = is
         , mDecls    = ds
         }

ufToNamed :: UpdField PName -> ParseM (Named (Expr PName))
ufToNamed (UpdField h ls e) =
  case (h,ls) of
    (UpdSet, [l]) | RecordSel i Nothing <- thing l ->
      pure Named { name = l { thing = i }, value = e }
    _ -> errorMessage (srcRange (head ls))
            "Invalid record field.  Perhaps you meant to update a record?"

selExprToSels :: Expr PName -> ParseM [Located Selector]
selExprToSels e0 = reverse <$> go noLoc e0
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
      ELit (ECNum n _) ->
        pure [ Located { thing = TupleSel (fromInteger n) Nothing
                       , srcRange = loc } ]
      _ -> errorMessage loc "Invalid label in record update."




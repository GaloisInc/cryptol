-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}
module Cryptol.Parser.ParserUtils where

import Cryptol.Parser.AST
import Cryptol.Parser.Lexer
import Cryptol.Parser.Position
import Cryptol.Parser.Utils (translateExprToNumT)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic

import Data.Maybe(listToMaybe,fromMaybe)
import Data.Bits(testBit,setBit)
import Control.Monad(liftM,ap,unless)
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>),Applicative(..))
import Data.Traversable (mapM)
import Prelude hiding (mapM)
#endif

parseString :: Config -> ParseM a -> String -> Either ParseError a
parseString cfg p cs = parse cfg p (T.pack cs)

parse :: Config -> ParseM a -> Text -> Either ParseError a
parse cfg p cs    = case unP p cfg eofPos (S toks) of
                      Left err    -> Left err
                      Right (a,_) -> Right a
  where (toks,eofPos) = lexer cfg cs


{- The parser is parameterized by the pozition of the final token. -}
data ParseM a   = P { unP :: Config -> Position -> S -> Either ParseError (a,S) }


lexerP :: (Located Token -> ParseM a) -> ParseM a
lexerP k = P $ \cfg p (S ts) ->
  case ts of
    t : _ | Err e <- tokenType it ->
      Left $ HappyErrorMsg (srcRange t) $
         case e of
           UnterminatedComment -> "unterminated comment"
           UnterminatedString  -> "unterminated string"
           UnterminatedChar    -> "unterminated character"
           InvalidString       -> "invalid string literal: " ++ T.unpack (tokenText it)
           InvalidChar         -> "invalid character literal: " ++ T.unpack (tokenText it)
           LexicalError        -> "unrecognized character: " ++ T.unpack (tokenText it)
      where it = thing t

    t : more -> unP (k t) cfg p (S more)
    []       -> Left (HappyError (cfgSource cfg) p Nothing)

data ParseError = HappyError FilePath Position (Maybe Token)
                | HappyErrorMsg Range String
                  deriving Show

newtype S = S [Located Token]

instance PP ParseError where
  ppPrec _ (HappyError _ _ tok) = case tok of
                                  Nothing -> text "end of input"
                                  Just t  -> pp t
  ppPrec _ (HappyErrorMsg _ x) = text x

ppError :: ParseError -> Doc
ppError (HappyError path pos (Just tok))
  | Err _ <- tokenType tok = text "Parse error at" <+>
                              text path <> char ':' <> pp pos <> comma <+>
                              pp tok
ppError e@(HappyError path pos _) =
                               text "Parse error at" <+>
                               text path <> char ':' <> pp pos <> comma <+>
                               text "unexpected" <+> pp e
ppError (HappyErrorMsg p x)  = text "Parse error at" <+> pp p $$ nest 2 (text x)

instance Monad ParseM where
  return a  = P (\_ _ s -> Right (a,s))
  fail s    = panic "[Parser] fail" [s]
  m >>= k   = P (\cfg p s1 -> case unP m cfg p s1 of
                            Left e       -> Left e
                            Right (a,s2) -> unP (k a) cfg p s2)

instance Functor ParseM where
  fmap = liftM

instance Applicative ParseM where
  pure  = return
  (<*>) = ap

happyError :: ParseM a
happyError = P $ \cfg p (S ls) ->
  Left $ case listToMaybe ls of
           Nothing -> HappyError (cfgSource cfg) p Nothing
           Just l  -> HappyError (cfgSource cfg) (from (srcRange l)) (Just (thing l))

errorMessage :: Range -> String -> ParseM a
errorMessage r x = P $ \_ _ _ -> Left (HappyErrorMsg r x)

customError :: String -> Located Token -> ParseM a
customError x t = P $ \_ _ _ -> Left (HappyErrorMsg (srcRange t) x)

mkModName :: LQName -> Located ModName
mkModName  = fmap $ \ (QName mb (Name n)) ->
  case mb of
    Just (ModName ns) -> ModName (ns ++ [n])
    Nothing           -> ModName [n]

mkQName :: {-reversed-} [LName] -> Located QName
mkQName [x] = fmap mkUnqual x
mkQName xs =
  Located { srcRange = rComb (srcRange f) (srcRange l)
          , thing    = mkQual (ModName [ x | Name x <- map thing ns ]) (thing l)
          }
  where l : ls      = xs
        ns@(f : _)  = reverse ls

-- Note that type variables are not resolved at this point: they are tcons.
mkSchema :: [TParam] -> [Prop] -> Type -> Schema
mkSchema xs ps t = Forall xs ps t Nothing

getName :: Located Token -> Name
getName l = case thing l of
              Token (Ident [] x) _ -> Name x
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

numLit :: TokenT -> Expr
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

mkFixity :: Assoc -> Located Token -> [LName] -> ParseM Decl
mkFixity assoc tok qns =
  do l <- intVal tok
     unless (l >= 1 && l <= 100)
          (errorMessage (srcRange tok) "Fixity levels must be between 0 and 20")
     return (DFixity (Fixity assoc (fromInteger l)) (map (fmap mkUnqual) qns))

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


validDemotedType :: Range -> Type -> ParseM Type
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
    TInf         -> bad "Infinity type"
    TWild        -> bad "Wildcard types"
    TUser {}     -> ok
    TApp {}      -> ok

    TParens t    -> validDemotedType rng t
    TInfix{}     -> ok

  where bad x = errorMessage rng (x ++ " cannot be demoted.")
        ok    = return $ at rng ty

mkEApp :: [Expr] -> Expr
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


unOp :: Expr -> Expr -> Expr
unOp f x = at (f,x) $ EApp f x

-- Use defaultFixity as a placeholder, it will be fixed during renaming.
binOp :: Expr -> Located QName -> Expr -> Expr
binOp x f y = at (x,y) $ EInfix x f defaultFixity y

eFromTo :: Range -> Expr -> Maybe Expr -> Maybe Expr -> ParseM Expr
eFromTo r e1 e2 e3 = EFromTo <$> exprToNumT r e1
                             <*> mapM (exprToNumT r) e2
                             <*> mapM (exprToNumT r) e3
exprToNumT :: Range -> Expr -> ParseM Type
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
anonRecord :: Maybe Range -> [Type] -> Type
anonRecord ~(Just r) ts = TRecord (map toField ts)
  where noName    = Located { srcRange = r, thing = Name "" }
        toField t = Named { name = noName, value = t }

exportDecl :: Maybe (Located String) -> ExportType -> Decl -> TopDecl
exportDecl mbDoc e d = Decl TopLevel { tlExport = e
                                     , tlDoc    = mbDoc
                                     , tlValue  = d }

exportNewtype :: ExportType -> Newtype -> TopDecl
exportNewtype e n = TDNewtype TopLevel { tlExport = e
                                       , tlDoc    = Nothing
                                       , tlValue  = n }

changeExport :: ExportType -> [TopDecl] -> [TopDecl]
changeExport e = map change
  where
  change (Decl d)      = Decl      d { tlExport = e }
  change (TDNewtype n) = TDNewtype n { tlExport = e }
  change td@Include{}  = td

mkTypeInst :: Named Type -> TypeInst
mkTypeInst x | thing (name x) == Name "" = PosInst (value x)
             | otherwise                 = NamedInst x


mkTParam :: Located Name -> Maybe Kind -> ParseM TParam
mkTParam Located { srcRange = rng, thing = n } k
  | Name "width" <- n = errorMessage rng "`width` is not a valid type parameter name."
  | otherwise = return (TParam n k (Just rng))

mkTySyn :: Located Name -> [TParam] -> Type -> ParseM Decl
mkTySyn n ps b
  | Name "width" <- thing n = errorMessage (srcRange n) "`width` is not a valid type synonym name."
  | otherwise = return $ DType $ TySyn (fmap mkUnqual n) ps b

polyTerm :: Range -> Integer -> Integer -> ParseM (Bool, Integer)
polyTerm rng k p
  | k == 0          = return (False, p)
  | k == 1          = return (True, p)
  | otherwise       = errorMessage rng "Invalid polynomial coefficient"

mkPoly :: Range -> [ (Bool,Integer) ] -> ParseM Expr
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
mkProperty :: LName -> [Pattern] -> Expr -> Decl
mkProperty f ps e = DBind Bind { bName       = fmap mkUnqual f
                               , bParams     = reverse ps
                               , bDef        = at e (Located emptyRange (DExpr (ETyped e TBit)))
                               , bSignature  = Nothing
                               , bPragmas    = [PragmaProperty]
                               , bMono       = False
                               , bInfix      = False
                               , bFixity     = Nothing
                               , bDoc        = Nothing
                               }

mkIf :: [(Expr, Expr)] -> Expr -> Expr
mkIf ifThens theElse = foldr addIfThen theElse ifThens
    where
    addIfThen (cond, doexpr) elseExpr = EIf cond doexpr elseExpr

-- | Generate a signature and a primitive binding.  The reason for generating
-- both instead of just adding the signature at this point is that it means the
-- primitive declarations don't need to be treated differently in the noPat
-- pass.  This is also the reason we add the doc to the TopLevel constructor,
-- instead of just place it on the binding directly.  A better solution might be
-- to just have a different constructor for primitives.
mkPrimDecl :: Maybe (Located String) -> Bool -> LName -> Schema -> [TopDecl]
mkPrimDecl mbDoc isInfix n sig =
  [ exportDecl mbDoc Public
    $ DBind Bind { bName      = qname
                 , bParams    = []
                 , bDef       = at sig (Located emptyRange DPrim)
                 , bSignature = Nothing
                 , bPragmas   = []
                 , bMono      = False
                 , bInfix     = isInfix
                 , bFixity    = Nothing
                 , bDoc       = Nothing
                 }
  , exportDecl Nothing Public
    $ DSignature [qname] sig
  ]
  where
  qname = fmap mkUnqual n

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
         $ T.dropWhileEnd (`elem` "/* \r\n\t")
         $ thing ltxt

  trimFront []                     = []
  trimFront (l:ls)
    | T.all (`elem` "/* \r\n\t") l = ls
    | otherwise                    = T.dropWhile (`elem` "/* ") l : ls

  dropPrefix []        = []
  dropPrefix [t]       = [T.dropWhile (`elem` "/* ") t]
  dropPrefix ts@(l:ls) =
    case T.uncons l of
      Just (c,_) | all (commonPrefix c) ls -> dropPrefix (map (T.drop 1) ts)
      _                                    -> ts

    where
    commonPrefix c t =
      case T.uncons t of
        Just (c',_) -> c == c'
        Nothing     -> False


mkProp :: Type -> ParseM (Located [Prop])
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
      TInf{}    -> err
      TWild     -> err
      TRecord{} -> err

    where
    err = errorMessage r "Invalid constraint"

  -- we have to delay these until renaming, when we have the fixity table
  -- present
  infixProp t = return [CType t]

  -- these can be translated right away
  prefixProp r f xs =
    case f of
      QName Nothing (Name "Arith") | [x] <- xs ->
        return [CLocated (CArith x) r]

      QName Nothing (Name "fin") | [x] <- xs ->
        return [CLocated (CFin x) r]

      QName Nothing (Name "Cmp") | [x] <- xs ->
        return [CLocated (CCmp x) r]

      _ -> errorMessage r "Invalid constraint"

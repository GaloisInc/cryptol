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
import Cryptol.Prims.Syntax
import Cryptol.Parser.Utils (translateExprToNumT)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic

import Data.Maybe(listToMaybe,fromMaybe)
import Data.Bits(testBit,setBit)
import Control.Monad(liftM,ap)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>),Applicative(..))
import Data.Traversable (mapM)
import Prelude hiding (mapM)
#endif

parse :: Config -> ParseM a -> String -> Either ParseError a
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
           InvalidString       -> "invalid string literal: " ++ tokenText it
           InvalidChar         -> "invalid character literal: " ++ tokenText it
           LexicalError        -> "lexical error: " ++ tokenText it
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

mkModName :: {-reversed-} [LName] -> Located ModName
mkModName xs = Located { srcRange = rComb (srcRange f) (srcRange l)
                       , thing    = ModName [ x | Name x <- map thing ns ]
                       }
  where l : _       = xs
        ns@(f : _)  = reverse xs

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
              Token (Ident x) _ -> Name x
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


op :: ECon -> Range -> Expr
op s r = at r (ECon s)

unOp :: Expr -> Expr -> Expr
unOp f x = at (f,x) $ EApp f x

binOp :: Expr -> Expr -> Expr -> Expr
binOp x f y = at (x,y) $ EApp (EApp f x) y

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

exportDecl :: ExportType -> Decl -> TopDecl
exportDecl e d = Decl TopLevel { tlExport = e, tlValue = d }

exportNewtype :: ExportType -> Newtype -> TopDecl
exportNewtype e n = TDNewtype TopLevel { tlExport = e, tlValue = n }

changeExport :: ExportType -> [TopDecl] -> [TopDecl]
changeExport e = map $ \ td -> case td of
  Decl d      -> Decl      d { tlExport = e }
  TDNewtype n -> TDNewtype n { tlExport = e }
  Include _   -> td

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
                               , bDef        = ETyped e TBit
                               , bSignature  = Nothing
                               , bPragmas    = [PragmaProperty]
                               , bMono       = False
                               }

mkIf :: [(Expr, Expr)] -> Expr -> Expr
mkIf ifThens theElse = foldr addIfThen theElse ifThens
    where
    addIfThen (cond, doexpr) elseExpr = EIf cond doexpr elseExpr

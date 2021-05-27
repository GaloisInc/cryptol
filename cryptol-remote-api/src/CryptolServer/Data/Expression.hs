{-# OPTIONS_GHC -fno-warn-type-defaults -Wno-missing-deriving-strategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Data.Expression
  ( module CryptolServer.Data.Expression
  ) where

import Control.Applicative
import Control.Monad.IO.Class
import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as Base64
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Scientific as Sc
import Data.Text (Text, pack)
import qualified Data.Text as T
import Data.Traversable
import Data.Typeable (Proxy(..), typeRep)
import qualified Data.Vector as V
import Data.Text.Encoding (encodeUtf8)
import Numeric (showHex)

import Cryptol.Backend.Monad
import qualified Cryptol.Eval.Concrete as Concrete
import Cryptol.Backend.SeqMap (enumerateSeqMap)
import Cryptol.Backend.WordValue (asWordVal)

import Cryptol.Eval (evalSel)
import Cryptol.Eval.Concrete (Value)
import Cryptol.Eval.Type (TValue(..), tValTy)
import Cryptol.Eval.Value (GenValue(..))
import Cryptol.ModuleSystem
  (ModuleEnv, ModuleCmd, getPrimMap, evalDecls, renameType, renameVar, checkExpr, focusedEnv)
import Cryptol.ModuleSystem.Env (deNames,meDynEnv, mctxParams, mctxDecls, mctxNames)
import Cryptol.ModuleSystem.Monad (runModuleM, interactive, getFocusedEnv)
import qualified Cryptol.ModuleSystem.Base as Base
import qualified Cryptol.ModuleSystem.Renamer as R
import Cryptol.ModuleSystem.Name
  (Name, mkDeclared, NameSource( UserName ), liftSupply, nameIdent)
import Cryptol.ModuleSystem.NamingEnv (singletonE, shadowing)

import qualified Cryptol.Parser as CP
import qualified Cryptol.Parser.AST as CP
import Cryptol.Parser.Position (Located(..), emptyRange)
import Cryptol.Parser.Selector
import qualified Cryptol.TypeCheck as TC
import qualified Cryptol.TypeCheck.AST as TC
import Cryptol.Utils.Ident
import Cryptol.Utils.RecordMap (recordFromFields, canonicalFields)

import Argo
import qualified Argo.Doc as Doc
import CryptolServer
import CryptolServer.Exceptions
import CryptolServer.Data.FreshName
import CryptolServer.Data.Type

data Encoding = Base64 | Hex
  deriving (Eq, Show, Ord)

instance JSON.FromJSON Encoding where
  parseJSON =
    withText "encoding" $
    \case
      "hex"    -> pure Hex
      "base64" -> pure Base64
      _        -> empty

data LetBinding =
  LetBinding
  { argDefName :: !Text
  , argDefVal  :: !Expression
  }
  deriving (Eq, Show)

instance JSON.FromJSON LetBinding where
  parseJSON =
    withObject "let binding" $ \o ->
      LetBinding <$> o .: "name" <*> o .: "definition"

instance JSON.ToJSON LetBinding where
  toJSON (LetBinding x def) =
    object [ "name" .= x
           , "definition" .= def
           ]

-- | Cryptol expressions which can be serialized into JSON and sent
-- to an RPC client.
data Expression =
    Bit !Bool
  | Unit
  | Num !Encoding !Text !Integer -- ^ data and bitwidth
  | Record !(HashMap Text Expression)
  | Sequence ![Expression]
  | Tuple ![Expression]
  | Integer !Integer
  | IntegerModulo !Integer !Integer -- ^ value, modulus
  | UniqueName !FreshName
    -- ^ Essentially a Cryptol.ModuleSystem.Name's nameUnique and nameIdent.
    -- Used when we need to send a result back to an RPC client
  | Concrete !Text -- ^ Concrete Cryptol syntax as a string -- the Cryptol parser
                   -- will establish it's meaning based on the current focus/context
  | Application !Expression !(NonEmpty Expression)
  | TypeApplication !Expression !TypeArguments
  deriving (Eq, Show)

newtype TypeArguments = TypeArguments (Map Ident JSONPType)
  deriving (Eq, Show) via Map Ident (CP.Type CP.PName)

data ExpressionTag
  = TagNum
  | TagRecord
  | TagSequence
  | TagTuple
  | TagUnit
  | TagApp
  | TagTypeApp
  | TagIntMod
  | TagUniqueName

instance JSON.FromJSON ExpressionTag where
  parseJSON =
    withText "tag" $
    \case
      "bits"           -> pure TagNum
      "unit"           -> pure TagUnit
      "record"         -> pure TagRecord
      "sequence"       -> pure TagSequence
      "tuple"          -> pure TagTuple
      "call"           -> pure TagApp
      "instantiate"    -> pure TagTypeApp
      "integer modulo" -> pure TagIntMod
      "unique name"    -> pure TagUniqueName
      _                -> empty

instance JSON.ToJSON ExpressionTag where
  toJSON TagNum        = "bits"
  toJSON TagRecord     = "record"
  toJSON TagSequence   = "sequence"
  toJSON TagTuple      = "tuple"
  toJSON TagUnit       = "unit"
  toJSON TagApp        = "call"
  toJSON TagTypeApp    = "instantiate"
  toJSON TagIntMod     = "integer modulo"
  toJSON TagUniqueName = "unique name"

instance JSON.FromJSON TypeArguments where
  parseJSON =
    withObject "type arguments" $ \o ->
      TypeArguments . Map.fromList <$>
        traverse elt (HM.toList o)
    where
      elt (name, ty) = (mkIdent name,) <$> parseJSON ty

instance JSON.FromJSON Expression where
  parseJSON v = bool v <|> integer v <|> concrete v <|> obj v
    where
      bool =
        withBool "boolean" $ pure . Bit
      integer =
        -- Note: this means that we should not expose this API to the
        -- public, but only to systems that will validate input
        -- integers. Otherwise, they can use this to allocate a
        -- gigantic integer that fills up all memory.
        withScientific "integer" $ \s ->
          case Sc.floatingOrInteger s of
            Left _fl -> empty
            Right i -> pure (Integer i)
      concrete =
        withText "concrete syntax" $ pure . Concrete

      obj =
        withObject "argument" $
        \o -> o .: "expression" >>=
              \case
                TagUnit -> pure Unit
                TagNum ->
                  do enc <- o .: "encoding"
                     Num enc <$> o .: "data" <*> o .: "width"
                TagRecord ->
                  do fields <- o .: "data"
                     flip (withObject "record data") fields $
                       \fs -> Record <$> traverse parseJSON fs
                TagSequence ->
                  do contents <- o .: "data"
                     flip (withArray "sequence") contents $
                       \s -> Sequence . V.toList <$> traverse parseJSON s
                TagTuple ->
                  do contents <- o .: "data"
                     flip (withArray "tuple") contents $
                       \s -> Tuple . V.toList <$> traverse parseJSON s
                TagApp ->
                  Application <$> o .: "function" <*> o .: "arguments"
                TagTypeApp ->
                  TypeApplication <$> o .: "generic" <*> o .: "arguments"
                TagIntMod ->
                  IntegerModulo <$> o .: "integer" <*> o .: "modulus"
                TagUniqueName -> do
                  contents <- o .: "unique"
                  ident <- o .: "identifier"
                  pure $ UniqueName $ unsafeFreshName contents ident

instance ToJSON Encoding where
  toJSON Hex = String "hex"
  toJSON Base64 = String "base64"

instance JSON.ToJSON Expression where
  toJSON Unit = object [ "expression" .= TagUnit ]
  toJSON (Bit b) = JSON.Bool b
  toJSON (Integer i) = JSON.Number (fromInteger i)
  toJSON (IntegerModulo i n) =
    object [ "expression" .= TagIntMod
           , "integer" .= JSON.Number (fromInteger i)
           , "modulus" .= JSON.Number (fromInteger n)
           ]
  toJSON (Concrete expr) = toJSON expr
  toJSON (Num enc dat w) =
    object [ "expression" .= TagNum
           , "data" .= String dat
           , "encoding" .= enc
           , "width" .= w
           ]
  toJSON (Record fields) =
    object [ "expression" .= TagRecord
           , "data" .= object [ fieldName .= toJSON val
                              | (fieldName, val) <- HM.toList fields
                              ]
           ]
  toJSON (Sequence elts) =
    object [ "expression" .= TagSequence
           , "data" .= Array (V.fromList (map toJSON elts))
           ]
  toJSON (Tuple projs) =
    object [ "expression" .= TagTuple
           , "data" .= Array (V.fromList (map toJSON projs))
           ]
  toJSON (Application fun args) =
    object [ "expression" .= TagApp
           , "function" .= fun
           , "arguments" .= args
           ]
  toJSON (UniqueName nm) =
    object [ "expression" .= TagUniqueName
           , "unique" .= toJSON (freshNameUnique nm)
           , "identifier" .= toJSON (freshNameText nm)
           ]
  toJSON (TypeApplication _gen (TypeArguments _args)) =
    -- Presumably this is dead code, since values are what are sent back to
    -- the user and type applications won't appear there ever.
    error "JSON conversion of type applications is not yet supported"


instance Doc.Described Expression where
  typeName = "JSON Cryptol Expressions"
  description =
    [ Doc.Paragraph [Doc.Text "In the API, Cryptol expressions can be represented by the following:"]
    , Doc.DescriptionList
        [ (pure $ Doc.Text "JSON Booleans",
           Doc.Paragraph [Doc.Text "Represent the corresponding Cryptol Booleans"])
        , (pure $ Doc.Text "JSON Integers",
           Doc.Paragraph [Doc.Text "Cryptol integer literals, that can be used at a variety of types"])
        , (pure $ Doc.Text "JSON Strings",
           Doc.Paragraph [Doc.Text "Cryptol concrete syntax"])
        , (pure $ Doc.Text "JSON Objects",
           Doc.Paragraph [ Doc.Text "Objects can represent a variety of Cryptol expressions. The field "
                         , Doc.Literal "expression"
                         , Doc.Text " contains a tag that can be used to determine the remaining fields."
                         ])
        ]
    , Doc.Paragraph [Doc.Text "The tag values in objects can be:"]
    , Doc.DescriptionList
        [ (pure $ Doc.Literal "bits",
           Doc.BulletedList
             [ Doc.Paragraph [Doc.Text "The expression is a bitvector. Further fields are:"]
             , Doc.Paragraph [ Doc.Literal "encoding", Doc.Text ": Either the string "
                             , Doc.Literal "base64", Doc.Text " or ", Doc.Literal "hex"
                             , Doc.Text ", for base-64 or hexadecimal representations of the bitvector"
                             ]
             , Doc.Paragraph [Doc.Literal "data", Doc.Text ": A string containing the actual data"]
             , Doc.Paragraph [Doc.Literal "width", Doc.Text ": An integer: the bit-width of the represented bit vector"]
             ])
        , (pure $ Doc.Literal "record",
           Doc.Paragraph [ Doc.Text "The expression is a record. The field "
                         , Doc.Literal "data", Doc.Text " is a JSON object that maps record field names to "
                         , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expressions"
                         , Doc.Text "."
                         ])
        , (pure $ Doc.Literal "sequence",
           Doc.Paragraph [ Doc.Text "The expression is a sequence. The field "
                         , Doc.Literal "data"
                         , Doc.Text "contains a JSON array of the elements of the sequence; "
                         , Doc.Text "each is a JSON Cryptol expression."
                         ])
        , (pure $ Doc.Literal "tuple",
           Doc.Paragraph [ Doc.Text "The expression is a tuple. The field "
                         , Doc.Literal "data"
                         , Doc.Text "contains a JSON array of the elements of the tuple; "
                         , Doc.Text "each is a JSON Cryptol expression."
                         ])
        , (pure $ Doc.Literal "unit",
           Doc.Paragraph [Doc.Text "The expression is the unit constructor, and there are no further fields."])
        , (pure $ Doc.Literal "let",
           Doc.BulletedList
             [ Doc.Paragraph [ Doc.Text "The expression is a ", Doc.Literal "where"
                             , Doc.Text "binding. The fields are:"
                             ]
             , Doc.DescriptionList
                 [ (pure $ Doc.Literal "binders",
                    Doc.BulletedList
                      [ Doc.Paragraph [Doc.Text "A list of binders. Each binder is an object with two fields:"]
                      , Doc.Paragraph [ Doc.Literal "name"
                                      , Doc.Text ": A string that is the name to be bound, and"
                                      ]
                      , Doc.Paragraph [ Doc.Literal "definition"
                                      , Doc.Text "A "
                                      , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expression"
                                      , Doc.Text "."
                                      ]
                     ])
                 , (pure $ Doc.Literal "body",
                    Doc.Paragraph [ Doc.Text "A "
                                  , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expression"
                                  , Doc.Text " in which the bound names may be used."
                                  ])
                 ]
             ])
        , (pure $ Doc.Literal "call",
           Doc.BulletedList
             [ Doc.Paragraph [Doc.Text "The expression is a function application. Further fields are:"]
             , Doc.Paragraph [ Doc.Literal "function", Doc.Text ": A "
                             , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expression"
                             , Doc.Text "."
                             ]
             , Doc.Paragraph [ Doc.Literal "arguments", Doc.Text ": A JSON array of "
                             , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expressions"
                             , Doc.Text "."
                             ]
             ])
        , (pure $ Doc.Literal "instantiate",
           Doc.BulletedList
             [ Doc.Paragraph [Doc.Text "The expression is a type application. Further fields are:"]
             , Doc.Paragraph [ Doc.Literal "generic"
                             , Doc.Text ": The polymorphic expression to be instantiated"
                             ]
             , Doc.Paragraph [ Doc.Literal "arguments"
                             , Doc.Text ": A JSON object in which keys are the names of type parameters and values are "
                             , Doc.Link (Doc.TypeDesc (typeRep (Proxy @JSONSchema))) "JSON Cryptol types"
                             , Doc.Text "."
                             ]
             ])
        , (pure $ Doc.Literal "integer modulo",
           Doc.BulletedList
             [ Doc.Paragraph [ Doc.Text "The expression is an integer with a modulus (the Cryptol "
                             , Doc.Literal "Z", Doc.Text " type). Further fields are:"
                             ]
             , Doc.Paragraph [ Doc.Literal "integer"
                             , Doc.Text ": A JSON number, representing the integer"
                             ]
             , Doc.Paragraph [ Doc.Literal "modulus"
                             , Doc.Text ": A JSON number, representing the modulus"
                             ]
             ])
        ]
    ]


decode ::
  (Monad m) =>
  (forall a. JSONRPCException -> m a) ->
  Encoding ->
  Text ->
  m Integer
decode raiseJSONErr Base64 txt =
  let bytes = encodeUtf8 txt
  in
    case Base64.decode bytes of
      Left err -> raiseJSONErr (invalidBase64 bytes err)
      Right decoded -> pure $ bytesToInt decoded
decode raiseJSONErr Hex txt =
  squish <$> traverse (hexDigit raiseJSONErr) (T.unpack txt)
  where
    squish = foldl (\acc i -> (acc * 16) + i) 0

hexDigit ::
  (Monad m, Num a) =>
  (forall b. JSONRPCException -> m b) ->
  Char ->
  m a
hexDigit raiseJSONErr =
  \case
    '0' -> pure 0
    '1' -> pure 1
    '2' -> pure 2
    '3' -> pure 3
    '4' -> pure 4
    '5' -> pure 5
    '6' -> pure 6
    '7' -> pure 7
    '8' -> pure 8
    '9' -> pure 9
    'a' -> pure 10
    'A' -> pure 10
    'b' -> pure 11
    'B' -> pure 11
    'c' -> pure 12
    'C' -> pure 12
    'd' -> pure 13
    'D' -> pure 13
    'e' -> pure 14
    'E' -> pure 14
    'f' -> pure 15
    'F' -> pure 15
    c   -> raiseJSONErr (invalidHex c)


-- | Given a textual unqualified type name as `Text`, get the corresponding
-- `Name` for the type in the current module environment.
getTypeName ::
  (Monad m) =>
  m ModuleEnv ->
  (forall a. ModuleCmd a -> m a) ->
  Text ->
  m Name
getTypeName getModEnv runModuleCmd ty = do
  nmEnv <- (mctxNames . focusedEnv) <$> getModEnv
  runModuleCmd $ renameType nmEnv (CP.UnQual (mkIdent ty))

getCryptolType ::
  (Monad m) =>
  m ModuleEnv ->
  (forall a. ModuleCmd a -> m a) ->
  JSONPType ->
  m (CP.Type Name)
getCryptolType getModEnv runModuleCmd (JSONPType rawTy) = do
  nmEnv <- (mctxNames . focusedEnv) <$> getModEnv
  runModuleCmd $ \env -> runModuleM env $ interactive $
    Base.rename interactiveName nmEnv (R.rename rawTy)

getExpr :: Expression -> CryptolCommand (CP.Expr Name)
getExpr = getCryptolExpr resolveFreshName
                         getModuleEnv
                         liftModuleCmd
                         CryptolServer.raise

-- N.B., used in SAWServer as well, hence the more generic monad and
-- parameterized monadic functions.
getCryptolExpr :: forall m.
  (Monad m) =>
  (FreshName -> m (Maybe Name)) {- ^ How to resolve a FreshName in the server. -} ->
  m ModuleEnv {- ^ Getter for Cryptol ModuleEnv. -} ->
  (forall a. ModuleCmd a -> m a) {- ^ Runner for Cryptol ModuleCmd. -} ->
  (forall a. JSONRPCException -> m a) {- ^ JSONRPCException error raiser. -} ->
  Expression {- Syntactic expression to convert to Cryptol. -} ->
  m (CP.Expr Name)
getCryptolExpr getName getModEnv runModuleCmd raiseJSONErr = go
  where
    go (UniqueName fnm) = do
      mNm <- getName fnm
      case mNm of
        Nothing -> raiseJSONErr $ unknownFreshName fnm
        Just nm -> pure $ CP.EVar nm
    go Unit =
      return $
        CP.ETyped
          (CP.ETuple [])
          (CP.TTuple [])
    go (Bit b) =
      return $ CP.ETyped
                  (if b
                    then CP.ELit $ CP.ECNum 1 (CP.BinLit "1" 1)
                    else CP.ELit $ CP.ECNum 0 (CP.BinLit "0" 0))
                  CP.TBit
    go (Integer i) = do
      intTy <- getTypeName getModEnv runModuleCmd "Integer"
      pure $
        CP.ETyped
          (CP.ELit (CP.ECNum i (CP.DecLit (pack (show i)))))
          (CP.TUser intTy [])
    go (IntegerModulo i n) = do
      zTy <- getTypeName getModEnv runModuleCmd "Z"
      return $
        CP.ETyped
          (CP.ELit (CP.ECNum i (CP.DecLit (pack (show i)))))
          (CP.TUser zTy [CP.TNum n])
    go (Num enc txt w) = do
        d <- decode raiseJSONErr enc txt
        return $ CP.ETyped
          (CP.ELit (CP.ECNum d (CP.DecLit txt)))
          (CP.TSeq (CP.TNum w) CP.TBit)
    go (Record fields) =
      fmap (CP.ERecord . recordFromFields) $ for (HM.toList fields) $
      \(recName, spec) ->
        (mkIdent recName,) . (emptyRange,) <$> go spec
    go (Sequence elts) =
      CP.EList <$> traverse go elts
    go (Tuple projs) =
      CP.ETuple <$> traverse go projs
    go (Concrete syntax) =
      case CP.parseExpr syntax of
        Left err ->
          raiseJSONErr $ cryptolParseErr syntax err
        Right e -> do
          (expr, _ty, _schema) <- runModuleCmd (checkExpr e)
          pure expr
    go (Application fun (arg :| [])) =
      CP.EApp <$> go fun <*> go arg
    go (Application fun (arg1 :| (arg : args))) =
      go (Application (Application fun (arg1 :| [])) (arg :| args))
    go (TypeApplication gen (TypeArguments args)) =
      CP.EAppT <$> go gen <*> (mapM inst (Map.toList args))
    inst (n, t) = do
      t' <- getCryptolType getModEnv runModuleCmd t
      pure $ CP.NamedInst (CP.Named (Located emptyRange n) t')

-- TODO add tests that this is big-endian
-- | Interpret a ByteString as an Integer
bytesToInt :: BS.ByteString -> Integer
bytesToInt bs =
  BS.foldl' (\acc w -> (acc * 256) + toInteger w) 0 bs

-- | Read back a typed value (if possible) into syntax which can be sent to an
-- RPC client. For some values which do not have a guaranteed syntactic
-- representation, a fresh variable will be generated and bound to
-- the value so the variable can instead be sent to the RPC client.
readBack :: TValue -> Value -> CryptolCommand (Maybe Expression)
readBack ty val =
  case ty of
    TVRec tfs -> do
      vals <- mapM readBackRecFld $ canonicalFields tfs
      pure $ (Record . HM.fromList) <$> sequence vals
    TVTuple [] ->
      pure $ Just Unit
    TVTuple ts -> do
      vals <- mapM readBackTupleFld $ zip [0..] ts
      pure $ Tuple <$> sequence vals
    TVBit ->
      case val of
        VBit b -> pure $ Just $ Bit b
        _ -> mismatchPanic
    TVInteger ->
      case val of
        VInteger i -> pure $ Just $ Integer i
        _ -> mismatchPanic
    TVIntMod n ->
      case val of
        VInteger i -> pure $ Just $ IntegerModulo i n
        _ -> mismatchPanic
    TVSeq len elemTy
      | elemTy == TVBit
      , VWord width wv <- val -> do
        Concrete.BV w v <- liftEval $ asWordVal Concrete.Concrete wv
        let hexStr = T.pack $ showHex v ""
        let paddedLen = fromIntegral ((width `quot` 4) + (if width `rem` 4 == 0 then 0 else 1))
        pure $ Just $  Num Hex (T.justifyRight paddedLen '0' hexStr) w
      | VSeq _l (enumerateSeqMap len -> mVals) <- val -> do
        vals <- liftEval $ sequence mVals
        es <- mapM (readBack elemTy) vals
        pure $ Sequence <$> sequence es

    _ -> do
      -- The above cases are for types that can unambiguously be converted into
      -- syntax; this case instead tries to essentially let-bind the value to a
      -- fresh variable so we can send that to the RPC client instead. They
      -- obviously won't be able to directly inspect the value, but they can
      -- pass it to other functions/commands via a RPC.
      mName <- bindValToFreshName (varName ty) ty val
      case mName of
        Nothing -> pure Nothing
        Just name -> pure $ Just $ UniqueName name
  where
    mismatchPanic :: CryptolCommand (Maybe Expression)
    mismatchPanic =
      error $ "Internal error: readBack: value '" <>
              show val <>
              "' didn't match type '" <>
              show (tValTy ty) <>
              "'"
    readBackRecFld :: (Ident, TValue) -> CryptolCommand (Maybe (Text, Expression))
    readBackRecFld (fldId, fldTy) = do
      fldVal <- liftEval $ evalSel Concrete.Concrete val (RecordSel fldId Nothing)
      fldExpr <- readBack fldTy fldVal
      pure $ (identText fldId,) <$> fldExpr
    readBackTupleFld :: (Int, TValue) -> CryptolCommand (Maybe Expression)
    readBackTupleFld (i, iTy) = do
      iVal <- liftEval $ evalSel Concrete.Concrete val (TupleSel i Nothing)
      readBack iTy iVal
    varName :: TValue -> Text
    varName =
      \case
        TVBit{} -> "bit"
        TVInteger{} -> "integer"
        TVFloat{} -> "float"
        TVIntMod n -> "z" <> (T.pack $ show n)
        TVRational{} -> "rational"
        TVArray{} -> "array"
        TVSeq{} -> "seq"
        TVStream{} -> "stream"
        TVTuple{} -> "tuple"
        TVRec{} -> "record"
        TVFun{} -> "fun"
        TVNewtype nt _ _ -> identText $ nameIdent $ TC.ntName nt
        TVAbstract{} -> "abstract"


-- | Given a suggested `name` and a type and value, attempt to bind the value
-- to a freshly generated name in the current server environment. If successful,
-- the generated name will be of the form `CryptolServer'nameN` (where `N` is a
-- natural number) and the `FreshName` that is returned can be serialized into an
-- `Expression` and sent to an RPC client.
bindValToFreshName :: Text -> TValue -> Concrete.Value -> CryptolCommand (Maybe FreshName)
bindValToFreshName nameBase ty val = do
  prims   <- liftModuleCmd getPrimMap
  mb      <- liftEval (Concrete.toExpr prims ty val)
  case mb of
    Nothing   -> return Nothing
    Just expr -> do
      name <- genFreshName
      fName <- registerName name
      let schema = TC.Forall { TC.sVars  = []
                             , TC.sProps = []
                             , TC.sType  = tValTy ty
                             }
          decl = TC.Decl { TC.dName       = name
                         , TC.dSignature  = schema
                         , TC.dDefinition = TC.DExpr expr
                         , TC.dPragmas    = []
                         , TC.dInfix      = False
                         , TC.dFixity     = Nothing
                         , TC.dDoc        = Nothing
                         }
      liftModuleCmd (evalDecls [TC.NonRecursive decl])
      modifyModuleEnv $ \me ->
        let denv = meDynEnv me
        in me {meDynEnv = denv { deNames = singletonE (CP.UnQual (nameIdent name)) name
                                             `shadowing` deNames denv }}
      return $ Just fName
  where
    genFreshName :: CryptolCommand Name
    genFreshName = do
      cnt <- freshNameCount
      let ident = mkIdent $ "CryptolServer'" <> nameBase <> (T.pack $ show cnt)
          mpath = TopModule interactiveName
      liftSupply (mkDeclared NSValue mpath UserName ident Nothing emptyRange)


liftEval :: Eval a -> CryptolCommand a
liftEval e = liftIO (runEval mempty e)

mkEApp :: CP.Expr Name -> [CP.Expr Name] -> CP.Expr Name
mkEApp f args = foldl CP.EApp f args



-- | Typecheck a single expression, yielding a typechecked core expression and a type schema.
typecheckExpr :: CP.Expr Name -> CryptolCommand (TC.Expr,TC.Schema)
typecheckExpr e = liftModuleCmd $ \env -> runModuleM env $ interactive $ do
  fe <- getFocusedEnv
  let params = mctxParams fe
      decls  = mctxDecls fe
  -- merge the dynamic and opened environments for typechecking
  prims <- Base.getPrimMap
  let act  = Base.TCAction { Base.tcAction = TC.tcExpr
                          , Base.tcLinter = Base.exprLinter
                          , Base.tcPrims = prims }
  (te,s) <- Base.typecheck act e params decls
  return (te,s)

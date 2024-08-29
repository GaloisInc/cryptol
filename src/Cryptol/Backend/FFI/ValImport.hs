{-# Language OverloadedStrings #-}
{-# Language BlockArguments #-}
{-# Language LambdaCase #-}
-- | Export builders for Cryptols values
module Cryptol.Backend.FFI.ValImport where

import Data.Text(Text)
import qualified Data.IntMap as IntMap
import Data.List(intersperse)
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Control.Exception
import Data.IORef
import Foreign
import Foreign.C.Types(CSize(..) )
import Control.Monad.Primitive(PrimState)
import GHC.Num(Integer(..))
import Data.Primitive.PrimArray(MutablePrimArray(..), PrimArray(..),
        mutablePrimArrayContents, newPinnedPrimArray, unsafeFreezePrimArray)  

import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Backend.Monad
import Cryptol.Backend.Concrete
import Cryptol.Backend.SeqMap

import Cryptol.Backend

data BuilderErrorMessage =
    ProtocolMismatch Thing Thing  -- ^ Expected, got
  | PartialValue
  | UnexpectedData
  | TagOutOfBounds Int
  | Unsupported Text
  | BadWordValue
  | BadRationalValue
  | FFINotEnabled
    deriving Show

data Thing = AValue | ATag | ASign
  deriving Show

type Value = SEval Concrete (GenValue Concrete)

-- | State of building a value (aka "context")
data Builder =
    Building [Frame]    -- ^ A partial value
  | Done Value          -- ^ Fully built value
  | Error BuilderErrorMessage
    -- ^ Something went wrong
    -- XXX: It'd be nice to store the [Frame] here as well,
    -- but that's a bit of a pain because of missing `Show` instances...

instance Exception BuilderErrorMessage

data Mk =
  Mk { mkPrec :: Int, mkPP :: [Doc] -> Doc
     , mkVal :: [Value] -> Either BuilderErrorMessage Value
     }

-- | Describes what we are missing
data Frame =
    NeedVal
    -- ^ A primitive value

  | NeedSign (MutablePrimArray (PrimState IO) Word64)
    -- ^ This is a step of making a BigInt.
    -- We've allocated a buffer and are waiting for it to be filled with the
    -- base-64 digits of of a big int (least significant first),
    -- and to be told what the sign should be.

  | NeedMany Mk [Value] [TValue]
    -- ^ A compound value, fields are like this:
    --  * Constructor for the value
    --  * Parts of the value we have
    --  * Types of the parts of the values we still need,
    --    not counting the hole.

  | NeedOneOf (Vector (ConInfo TValue))
    -- ^ Sum type value, which needs a constructor tag to proceed.

-- | Fill the "hole" with the given value.
haveValue :: Value -> [Frame] -> Builder
haveValue v fs =
  case fs of
    [] -> Done v
    f : more ->
      case f of
        NeedVal -> haveValue v more
        NeedMany mk vs ts ->
          let done = v : vs in
          case ts of
            [] -> case mkVal mk (reverse done) of
                    Left err -> Error err
                    Right a  -> haveValue a more
            t : ts' -> needValue t (NeedMany mk done ts' : more)
        NeedOneOf {} -> Error (ProtocolMismatch ATag AValue)
        NeedSign {} -> Error (ProtocolMismatch ASign AValue)

-- | Provide a constructor tag  
haveTag :: Int -> [Frame] -> Builder
haveTag n fs0 =
  case fs0 of
    [] -> Error UnexpectedData
    f : fs ->
      case f of
        NeedVal     -> Error (ProtocolMismatch AValue ATag)
        NeedMany {} -> Error (ProtocolMismatch AValue ATag)
        NeedSign {} -> Error (ProtocolMismatch ASign ATag)
        NeedOneOf opts ->
          case opts Vector.!? n of
            Nothing -> Error (TagOutOfBounds n)
            Just ci ->
              case Vector.toList (conFields ci) of
                [] -> haveValue (mkV []) fs
                t : ts ->
                  needValue t (NeedMany (Mk 10 ppV (Right . mkV)) [] ts : fs) 
              where
              ppV xs = pp (conIdent ci) <+> hsep xs 
     
              mkV :: [Value] -> Value
              mkV vs = pure (VEnum
                              (toInteger n)
                              (IntMap.singleton n
                                  ci { conFields = Vector.fromList vs }))


haveSign :: Bool -> [Frame] -> IO Builder
haveSign isPos fs0 =
  case fs0 of
    [] -> pure (Error UnexpectedData)
    f : fs ->
      case f of
        NeedVal -> mismatch AValue
        NeedMany {} -> mismatch AValue
        NeedOneOf {} -> mismatch ATag
        NeedSign buf ->                                                     
          do PrimArray fbuf <- unsafeFreezePrimArray buf                          
             let i = if isPos then IP fbuf else IN fbuf
             i `seq` pure (haveValue (pure (VInteger i)) fs)
  where
  mismatch x = pure (Error (ProtocolMismatch x ASign))         

-- | Make a "hole" of the given type.
needValue :: TValue -> [Frame] -> Builder
needValue tval fs =
  case tval of
    TVBit      -> Building (NeedVal : fs)
    TVInteger  -> Building (NeedVal : fs)
    TVIntMod _ -> Building (NeedVal : fs)
    TVFloat {} -> Building (NeedVal : fs)

    TVRational -> 
      Building (NeedVal : NeedMany (Mk 10 ppV mkV) [] [TVInteger] : fs)
        where
        ppV xs = "Rational" <+> hsep xs
        mkV xs =
          case xs of
            [Ready (VInteger i), Ready (VInteger j)] ->
              Right (VRational <$> ratio Concrete i j)
            _ -> Left BadRationalValue

    TVSeq len elT ->
      case elT of
        TVBit -> Building (NeedVal : NeedMany (Mk 10 ppV mkV) [] [] : fs)
          where
          ppV xs = "Word" <+> integer len <+> hsep xs
          mkV xs =
            case xs of
              [Ready (VInteger i)] -> Right (word Concrete len i)
              _ -> Left BadWordValue

        _ | len < 1 -> haveValue (mkV []) fs
          | otherwise ->
            needValue elT (NeedMany (Mk 0 ppV (Right . mkV)) [] ts : fs) 
          where
          ppV xs = brackets (commaSep xs)
          mkV xs = mkSeq Concrete (Nat len) elT (finiteSeqMap Concrete xs)
          ts = replicate (fromInteger len - 1) elT

    TVTuple tys ->
      case tys of
        [] -> haveValue (mkV []) fs
        t : ts -> needValue t (NeedMany (Mk 0 ppV (Right . mkV)) [] ts : fs)
        where
        ppV xs = parens (commaSep xs)
        mkV = pure . VTuple

    TVRec rmp -> doRec rmp

    TVNominal _ _ nv ->
      case nv of
        TVAbstract -> Error (Unsupported "abstract")
        TVStruct rmp -> doRec rmp
        TVEnum cons -> Building (NeedOneOf cons : fs)

    TVFun {}    -> Error (Unsupported "function")
    TVStream {} -> Error (Unsupported "infinite stream")
    TVArray {}  -> Error (Unsupported "array")

  where
  doRec rmp =
    case ts of
      [] -> haveValue (mkV []) fs
      t : ts' -> needValue t (NeedMany (Mk 0 ppV (Right . mkV)) [] ts' : fs)
    where
    (ls,ts) = unzip (canonicalFields rmp)
    mkV vs = pure (VRecord (recordFromFields (zip ls vs)))
    ppV xs = braces (commaSep (zipWith ppF ls xs))
    ppF x y = pp x <+> "_" <+> y


ppValPrec :: Int -> Value -> Doc
ppValPrec p v =
  case ppValuePrec Concrete defaultPPOpts p =<< v of
    Ready doc -> doc
    _ -> "<thunk>"

instance PP Frame where
  ppPrec _ f =
    case f of
      NeedVal -> "_"
      NeedMany mk vs ts ->
        let p = mkPrec mk
            args = map (ppValPrec p) vs ++ ["_"] ++ map (ppPrec p . tValTy) ts
        in mkPP mk args
      NeedOneOf vs ->
        hsep (intersperse "|" (map (pp . conIdent) (Vector.toList vs)))
      NeedSign {} -> "BigNum _"



--------------------------------------------------------------------------------

cryNewValueBuilder :: TValue -> IO (StablePtr (IORef Builder))
cryNewValueBuilder ty =
  do ref <- newIORef (needValue ty [])
     newStablePtr ref

cryFinishBuilder ::
  StablePtr (IORef Builder) -> IO (Either BuilderErrorMessage Value)
cryFinishBuilder ptr =
  do ref <- deRefStablePtr ptr
     freeStablePtr ptr
     builder <- readIORef ref
     pure $!
       case builder of
         Done v -> Right v
         Error e -> Left e
         Building _ -> Left PartialValue


--------------------------------------------------------------------------------




modifyState :: ([Frame] -> Builder) -> Ptr () -> IO ()
modifyState how ptr =
  do ref <- deRefStablePtr (castPtrToStablePtr ptr)
     modifyIORef ref \case
       Error err    -> Error err
       Done _       -> Error UnexpectedData
       Building fs  -> how fs


-- | This function assumes that we are the only ones modifying the
-- builder state, so we don't need to worry about race conditions.
modifyStateIO :: ([Frame] -> IO Builder) -> Ptr () -> IO ()
modifyStateIO how ptr =
  do ref <- deRefStablePtr (castPtrToStablePtr ptr)
     builder <- readIORef ref
     writeIORef ref =<<
       case builder of
         Error err    -> pure (Error err)
         Done _       -> pure (Error UnexpectedData)
         Building fs  -> how fs


type Export a = a -> Ptr () -> IO ()

-- | Receive a bool value
cry_bool :: Export Word8
cry_bool b = modifyState (haveValue $! v)
  where
  v = if b == 0 then pure (VBit False) else pure (VBit True)

-- | Receive an integer that fits in 64-bits
cry_small_int :: Export Word64
cry_small_int i = modifyState (haveValue $! v)
  where
  v = pure $! VInteger $! toInteger i

-- | Receive an integer that's larger than 64-bits.
-- This is part 1 of a 2 step process.
type LargeIntFun = Ptr () -> CSize -> IO (Ptr Word64)
cry_large_int :: LargeIntFun
cry_large_int ptr sz =
  do arr <- newPinnedPrimArray (fromIntegral sz)
     modifyState (\fs -> Building (NeedSign arr : fs)) ptr
     pure (mutablePrimArrayContents arr)

-- | Finish building a large integer.
-- The argument is 1 for negative, 0 for non-negative.
cry_sign :: Export Word8
cry_sign sign = modifyStateIO (haveSign (sign == 0))

-- | Receive a tag for a sum type.
cry_tag :: Export CSize
cry_tag c = modifyState (haveTag $! fromIntegral c)

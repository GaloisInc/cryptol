{-# Language OverloadedStrings #-}
{-# Language BlockArguments #-}
{-# Language LambdaCase #-}
-- | Export builders for Cryptols values
module Cryptol.Backend.FFI.Export where


import Data.Text(Text)
import qualified Data.IntMap as IntMap
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.IORef
import Foreign
import Foreign.C.Types

import Cryptol.Utils.RecordMap
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Backend.Concrete
import Cryptol.Backend.SeqMap

type Value = SEval Concrete (GenValue Concrete)

-- | State of building a value (aka "context")
data Builder =
    Building [Frame]    -- ^ A partial value
  | Done Value          -- ^ Fully built value
  | Error Text          -- ^ Something went wrong

-- | Describes what we are missing
data Frame =
    NeedVal
    -- ^ A primitive value

  | NeedMany ([Value] -> Value) [Value] [TValue]
    -- ^ A compound value, fields are like this:
    --  * Constructor for the value
    --  * Parts of the value we have
    --  * Types of the parts of the value we still need,
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
            [] -> haveValue (mk (reverse done)) more
            t : ts' -> needValue t (NeedMany mk done ts' : more)
        NeedOneOf {} -> Error "Got a value when expecting a tag."

-- | Provide a constructor tag  
haveTag :: Int -> [Frame] -> Builder
haveTag n fs0 =
  case fs0 of
    [] -> Error "Got a tag, but no value is being constructed."
    f : fs ->
      case f of
        NeedVal -> Error "Got a tag when expecting a value."
        NeedMany {} -> Error "Got a tag when expecting a compound value."
        NeedOneOf opts ->
          case opts Vector.!? n of
            Nothing -> Error "Tag out of bounds."
            Just ci ->
              case Vector.toList (conFields ci) of
                [] -> haveValue (mk []) fs
                t : ts -> needValue t (NeedMany mk [] ts : fs) 
              where
              mk :: [Value] -> Value
              mk vs = pure (VEnum
                              (toInteger n)
                              (IntMap.singleton n
                                  ci { conFields = Vector.fromList vs }))


-- | Make a "hole" of the given type.
needValue :: TValue -> [Frame] -> Builder
needValue tval fs =
  case tval of
    TVBit      -> Building (NeedVal : fs)
    TVInteger  -> Building (NeedVal : fs)
    TVIntMod _ -> Building (NeedVal : fs)
    TVRational -> Building (NeedVal : fs)
    TVFloat {} -> Building (NeedVal : fs)

    TVSeq len elT ->
      case elT of
        TVBit -> Building (NeedVal : fs)
        _ | len < 1 -> haveValue (mk []) fs
          | otherwise ->
            needValue elT (NeedMany mk [] ts : fs) 
        where
        mk xs = mkSeq Concrete (Nat len) elT (finiteSeqMap Concrete xs)
        ts = replicate (fromInteger len - 1) elT

    TVTuple tys ->
      case tys of
        [] -> haveValue (pure (VTuple [])) fs
        t : ts -> needValue t (NeedMany (pure . VTuple) [] ts : fs)

    TVRec rmp -> doRec rmp

    TVNominal _ _ nv ->
      case nv of
        TVAbstract -> Error "Abstract values are not supported."
        TVStruct rmp -> doRec rmp
        TVEnum cons -> Building (NeedOneOf cons : fs)

    TVFun {}    -> Error "Functionctions are not supported."
    TVStream {} -> Error "Infinite streams are not supported."
    TVArray {}  -> Error "Cryptol Array type is not supported."

  where
  doRec rmp =
    case ts of
      [] -> haveValue (mk []) fs
      t : ts' -> needValue t (NeedMany mk [] ts' : fs)
    where
    (ls,ts) = unzip (canonicalFields rmp)
    mk vs = pure (VRecord (recordFromFields (zip ls vs))) 




cryNewValueBuilder :: TValue -> IO (StablePtr (IORef Builder))
cryNewValueBuilder ty =
  do ref <- newIORef (needValue ty [])
     newStablePtr ref


modifyState :: ([Frame] -> Builder) -> Ptr () -> IO ()
modifyState how ptr =
  do ref <- deRefStablePtr (castPtrToStablePtr ptr)
     modifyIORef ref \case
       Error err    -> Error err
       Done _       -> Error "Unexpected data when finished."
       Building fs  -> how fs

type Export a = a -> Ptr () -> IO ()

foreign export ccall cry_bool :: Export CBool
cry_bool :: Export CBool
cry_bool b = modifyState (haveValue $! v)
  where
  v = if b == 0 then pure (VBit False) else pure (VBit True)

foreign export ccall cry_tag :: Export CInt
cry_tag :: Export CInt
cry_tag c = modifyState (haveTag $! fromIntegral c)


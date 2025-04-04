{-# Language OverloadedStrings, BangPatterns, MagicHash #-}
module Cryptol.Backend.FFI.ValExport
  ( ExportVal
  , ExporterErrorMessage(..)
  , Export
  , exportValue, exportValues
  , cryStartExport, cryEndExport
  , cry_recv_u8
  , cry_recv_u64
  , cry_recv_u64_digits
  ) where

import Data.Text(Text)
import qualified Data.Vector as Vector
import qualified Data.IntMap as IntMap
import Control.Exception(Exception,throw)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)
import Foreign
    ( Word8, Word32, Word64, StablePtr, Ptr, Storable(poke),
      newStablePtr, freeStablePtr, castPtrToStablePtr, deRefStablePtr )
import GHC.Num ( Integer(IN, IS, IP) )
import GHC.Base(Int(..))
import Data.Primitive.PrimArray
    ( copyPrimArrayToPtr, sizeofPrimArray, PrimArray(..) )

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.RecordMap ( canonicalFields )
import Cryptol.Eval.Value ( Backend(SWord, SEval), GenValue(..) )
import Cryptol.Eval.Type(conFields)
import Cryptol.Backend.Concrete ( BV(BV), Concrete(..) )
import Cryptol.Backend.Monad(Eval)
import Cryptol.Backend.SeqMap (enumerateSeqMap)
import Cryptol.Backend(SRational(..))
import Cryptol.Backend.WordValue(asWordVal)

data ExportVal =
    EV8 !Word8              -- ^ Bit, integer sign
  | EV64 !Word64            -- ^ Buffer size, sum tag
  | EVInteger !Integer      -- ^ Integer, Z, Word, components of Rational


data ExporterErrorMessage =
    UnsupportedValue Text
  | MalformedSum
  deriving Show

instance Exception ExporterErrorMessage

type Value = SEval Concrete (GenValue Concrete)

-- Serialize a value into its external representation.
exportValue :: GenValue Concrete -> [ExportVal] -> Eval [ExportVal]
exportValue v =
  case v of
    VRecord rmap -> doRec rmap
    VTuple vs    -> exportValues vs
    VSeq n sm    -> exportValues (enumerateSeqMap n sm)

    -- 1. tag, 2. constructo values
    VEnum tag mp
      | 0 <= tag && tag <= toInteger (maxBound :: Int)
      , let n = fromInteger tag
      , Just con <- IntMap.lookup n mp ->
        exportValues (Vector.toList (conFields con)) . (EV64 (fromIntegral n) :)

      | otherwise -> throw MalformedSum

    VBit b      -> pure . exportBit b
    VInteger i  -> pure . exportInteger i
    VRational r -> pure . exportRational r
    VFloat {}   -> throw (UnsupportedValue "XXX: Float")
    VWord w   -> \start ->
      do wv <- asWordVal Concrete w
         pure (exportWord wv start)
    
 
    VStream {}  -> throw (UnsupportedValue "infinte stream")
    VFun {}     -> throw (UnsupportedValue "function")
    VPoly {}    -> throw (UnsupportedValue "polymorphic")
    VNumPoly {} -> throw (UnsupportedValue "polymorphic")
  where
  doRec rmap = exportValues (map snd (canonicalFields rmap))


-- | Encoding of a bit: 0 or 1
exportBit :: Bool -> [ExportVal] -> [ExportVal]
exportBit b = (EV8 u8 :)
  where
  !u8 = if b then 1 else 0

-- | Encoding for an integer: sign, buffer size, digits
exportInteger :: Integer -> [ExportVal] -> [ExportVal]
exportInteger i = \start -> EVInteger i : EV64 size : EV8 sign : start
  where
  !sign = if i < 0 then 1 else 0
  !size = integerSize i

-- | Encoding of a rational: numerator, denominator; both are integers
exportRational :: SRational Concrete -> [ExportVal] -> [ExportVal]
exportRational r = exportInteger (sDenom r) . exportInteger (sNum r)

-- | Encoding of a word: buffer size, digits
exportWord :: SWord Concrete -> [ExportVal] -> [ExportVal]
exportWord (BV _ i) = \start -> EVInteger i : EV64 size : start
  where
  !size = integerSize i

-- | Export a sequence of values: tuples, recrods, sequnces.
-- Note that empty sequences don't have any representation.
exportValues :: [Value] -> [ExportVal] -> Eval [ExportVal]
exportValues vs done =
  case vs of
    mv : more ->
      do v <- mv
         exportValues more =<< exportValue v done
    [] -> pure done


-- | How many Word64s do we need to represent this integer.
integerSize :: Integer -> Word64
integerSize i =
  case i of
    IS _ -> 1
    IP x -> getSize (PrimArray x)
    IN x -> getSize (PrimArray x)
  where
  getSize :: PrimArray Word64 -> Word64
  getSize x = fromIntegral (sizeofPrimArray x)



cryStartExport ::
    [ExportVal] {-| REVERSED.  Send these to foreign. -} ->
    IO (StablePtr (IORef [ExportVal]))
cryStartExport vs =
  do ref <- newIORef (reverse vs)
     newStablePtr ref

-- | Get the next data item to export.
-- We assume that this is the only place to manipulate the reference
-- so there's not race condition. Note that it is also important
-- that we access these from the same thread, otherwise we may miss
-- some of the writes etc.  This should be OK because FFI calls should
-- all be happening on the same thread.
cryExportNext ::
  StablePtr (IORef [ExportVal]) -> IO (Either Word32 ExportVal)
cryExportNext ptr =
  do ref <- deRefStablePtr ptr
     xs  <- readIORef ref
     case xs of
       x : more -> writeIORef ref more >> pure (Right x)
       [] -> pure (Left maxBound)

cryEndExport :: StablePtr (IORef [ExportVal]) -> IO ()
cryEndExport = freeStablePtr


type Export a = Ptr () -> Ptr a -> IO Word32

-- | Get the next data item, which should be uint8_t
cry_recv_u8 :: Export Word8
cry_recv_u8 self out =
  do mb <- cryExportNext (castPtrToStablePtr self)
     case mb of
       Left err -> pure err
       Right d ->
         case d of
           EV8 w        -> poke out w >> pure 0
           EV64 {}      -> pure 2
           EVInteger {} -> pure 3
       

-- | Get the next data item, which shoudl be uint64_t
cry_recv_u64 :: Export Word64
cry_recv_u64 self out =
  do mb <- cryExportNext (castPtrToStablePtr self)
     case mb of
       Left err -> pure err
       Right d ->
         case d of
           EV8 {}       -> pure 1
           EV64 w       -> poke out w >> pure 0
           EVInteger {} -> pure 3
  

-- | Get the digits for an integer
cry_recv_u64_digits :: Export Word64
cry_recv_u64_digits self out =
  do mb <- cryExportNext (castPtrToStablePtr self)
     case mb of
       Left err -> pure err
       Right d ->
         case d of
           EV8 {}      -> pure 1
           EV64 {}     -> pure 2
           EVInteger i ->
             do case i of
                  IS x -> poke out (fromIntegral (abs (I# x)))
                  IP x -> doCopy (PrimArray x)
                  IN x -> doCopy (PrimArray x)
                pure 0
            where
            doCopy :: PrimArray Word64 -> IO ()
            doCopy x = copyPrimArrayToPtr out x 0 (sizeofPrimArray x)   
  
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Splittable
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of bit-vector concatanetation and splits
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE BangPatterns           #-}

module Data.SBV.BitVectors.Splittable (Splittable(..), FromBits(..)) where

import Data.Bits (Bits(..))
import Data.Word (Word8, Word16, Word32, Word64)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model

infixr 5 #
-- | Splitting an @a@ into two @b@'s and joining back.
-- Intuitively, @a@ is a larger bit-size word than @b@, typically double.
-- The 'extend' operation captures embedding of a @b@ value into an @a@
-- without changing its semantic value.
--
-- Minimal complete definition: All, no defaults.
class Splittable a b | b -> a where
  split  :: a -> (b, b)
  (#)    :: b -> b -> a
  extend :: b -> a

genSplit :: (Integral a, Num b) => Int -> a -> (b, b)
genSplit ss x = (fromIntegral ((ix `shiftR` ss) .&. mask), fromIntegral (ix .&. mask))
  where ix = toInteger x
        mask = 2 ^ ss - 1

genJoin :: (Integral b, Num a) => Int -> b -> b -> a
genJoin ss x y = fromIntegral ((ix `shiftL` ss) .|. iy)
  where ix = toInteger x
        iy = toInteger y

-- concrete instances
instance Splittable Word64 Word32 where
  split = genSplit 32
  (#)   = genJoin  32
  extend b = 0 # b

instance Splittable Word32 Word16 where
  split = genSplit 16
  (#)   = genJoin  16
  extend b = 0 # b

instance Splittable Word16 Word8 where
  split = genSplit 8
  (#)   = genJoin  8
  extend b = 0 # b

cwSplit :: (SymWord a, Num a) => CW -> (SBV a, SBV a)
cwSplit z@(CW _ (CWInteger v)) = (literal x, literal y)
  where (x, y) = genSplit (intSizeOf z `div` 2) v
cwSplit z = error $ "SBV.cwSplit: Unsupported CW value: " ++ show z

cwJoin :: (SymWord a, Num a) => CW -> CW -> SBV a
cwJoin x@(CW _ (CWInteger a)) (CW _ (CWInteger b)) = literal (genJoin (intSizeOf x) a b)
cwJoin x y = error $ "SBV.cwJoin: Unsupported arguments: " ++ show (x, y)

-- symbolic instances
instance Splittable SWord64 SWord32 where
  split (SBV _ (Left z)) = cwSplit z
  split z                = (SBV (KBounded False 32) (Right (cache x)), SBV (KBounded False 32) (Right (cache y)))
    where x st = do zsw <- sbvToSW st z
                    newExpr st (KBounded False 32) (SBVApp (Extract 63 32) [zsw])
          y st = do zsw <- sbvToSW st z
                    newExpr st (KBounded False 32) (SBVApp (Extract 31  0) [zsw])
  (SBV _ (Left a)) # (SBV _ (Left b)) = cwJoin a b
  a # b = SBV (KBounded False 64) (Right (cache c))
    where c st = do asw <- sbvToSW st a
                    bsw <- sbvToSW st b
                    newExpr st (KBounded False 64) (SBVApp Join [asw, bsw])
  extend b = 0 # b

instance Splittable SWord32 SWord16 where
  split (SBV _ (Left z)) = cwSplit z
  split z                = (SBV (KBounded False 16) (Right (cache x)), SBV (KBounded False 16) (Right (cache y)))
    where x st = do zsw <- sbvToSW st z
                    newExpr st (KBounded False 16) (SBVApp (Extract 31 16) [zsw])
          y st = do zsw <- sbvToSW st z
                    newExpr st (KBounded False 16) (SBVApp (Extract 15  0) [zsw])
  (SBV _ (Left a)) # (SBV _ (Left b)) = cwJoin a b
  a # b = SBV (KBounded False 32) (Right (cache c))
    where c st = do asw <- sbvToSW st a
                    bsw <- sbvToSW st b
                    newExpr st (KBounded False 32) (SBVApp Join [asw, bsw])
  extend b = 0 # b

instance Splittable SWord16 SWord8 where
  split (SBV _ (Left z)) = cwSplit z
  split z                = (SBV (KBounded False 8) (Right (cache x)), SBV (KBounded False 8) (Right (cache y)))
    where x st = do zsw <- sbvToSW st z
                    newExpr st (KBounded False 8) (SBVApp (Extract 15 8) [zsw])
          y st = do zsw <- sbvToSW st z
                    newExpr st (KBounded False 8) (SBVApp (Extract  7 0) [zsw])
  (SBV _ (Left a)) # (SBV _ (Left b)) = cwJoin a b
  a # b = SBV (KBounded False 16) (Right (cache c))
    where c st = do asw <- sbvToSW st a
                    bsw <- sbvToSW st b
                    newExpr st (KBounded False 16) (SBVApp Join [asw, bsw])
  extend b = 0 # b

-- | Unblasting a value from symbolic-bits. The bits can be given little-endian
-- or big-endian. For a signed number in little-endian, we assume the very last bit
-- is the sign digit. This is a bit awkward, but it is more consistent with the "reverse" view of
-- little-big-endian representations
--
-- Minimal complete definition: 'fromBitsLE'
class FromBits a where
 fromBitsLE, fromBitsBE :: [SBool] -> a
 fromBitsBE = fromBitsLE . reverse

-- | Construct a symbolic word from its bits given in little-endian
fromBinLE :: (Num a, Bits a, SymWord a) => [SBool] -> SBV a
fromBinLE = go 0 0
  where go !acc _  []     = acc
        go !acc !i (x:xs) = go (ite x (setBit acc i) acc) (i+1) xs

-- | Perform a sanity check that we should receive precisely the same
-- number of bits as required by the resulting type. The input is little-endian
checkAndConvert :: (Num a, Bits a, SymWord a) => Int -> [SBool] -> SBV a
checkAndConvert sz xs
  | sz /= l
  = error $ "SBV.fromBits.SWord" ++ ssz ++ ": Expected " ++ ssz ++ " elements, got: " ++ show l
  | True
  = fromBinLE xs
  where l   = length xs
        ssz = show sz

instance FromBits SBool where
 fromBitsLE [x] = x
 fromBitsLE xs  = error $ "SBV.fromBits.SBool: Expected 1 element, got: " ++ show (length xs)

instance FromBits SWord8  where fromBitsLE = checkAndConvert  8
instance FromBits SInt8   where fromBitsLE = checkAndConvert  8
instance FromBits SWord16 where fromBitsLE = checkAndConvert 16
instance FromBits SInt16  where fromBitsLE = checkAndConvert 16
instance FromBits SWord32 where fromBitsLE = checkAndConvert 32
instance FromBits SInt32  where fromBitsLE = checkAndConvert 32
instance FromBits SWord64 where fromBitsLE = checkAndConvert 64
instance FromBits SInt64  where fromBitsLE = checkAndConvert 64

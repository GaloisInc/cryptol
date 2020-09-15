-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Crypto.AES
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- An implementation of AES (Advanced Encryption Standard), using SBV.
-- For details on AES, see <http://en.wikipedia.org/wiki/Advanced_Encryption_Standard>.
--
-- We do a T-box implementation, which leads to good C code as we can take
-- advantage of look-up tables. Note that we make virtually no attempt to
-- optimize our Haskell code. The concern here is not with getting Haskell running
-- fast at all. The idea is to program the T-Box implementation as naturally and clearly
-- as possible in Haskell, and have SBV's code-generator generate fast C code automatically.
-- Therefore, we merely use ordinary Haskell lists as our data-structures, and do not
-- bother with any unboxing or strictness annotations. Thus, we achieve the separation
-- of concerns: Correctness via clarity and simplicity and proofs on the Haskell side,
-- performance by relying on SBV's code generator. If necessary, the generated code
-- can be FFI'd back into Haskell to complete the loop.
--
-- All 3 valid key sizes (128, 192, and 256) as required by the FIPS-197 standard
-- are supported.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Cryptol.AES where

import Data.Bits
import Data.List (transpose, genericTake, genericDrop, genericLength)
import Data.Word (Word8, Word32)

import Numeric (showHex)

-----------------------------------------------------------------------------
-- * Formalizing GF(2^8)
-----------------------------------------------------------------------------

-- | An element of the Galois Field 2^8, which are essentially polynomials with
-- maximum degree 7. They are conveniently represented as values between 0 and 255.
type GF28 = Word8


fromBitsLE :: [Bool] -> Word8
fromBitsLE [] = 0
fromBitsLE (False:bs) = fromBitsLE bs `shiftL` 1
fromBitsLE (True:bs)  = (fromBitsLE bs `shiftL` 1) + 1

blastLE :: Word8 -> [Bool]
blastLE w
  | w == 0 = []
  | w `mod` 2 == 0 = False : blastLE (w `shiftR` 1)
  | otherwise  = True  : blastLE (w `shiftR` 1)

-- | Multiply two polynomials and reduce by the third (concrete) irreducible, given by its coefficients.
-- See the remarks for the 'pMult' function for this design choice
pMult :: GF28 -> GF28 -> [Int] -> GF28
pMult x y red = fromBitsLE $ genericTake sz $ r ++ repeat False
  where (_, r) = mdp ms rs
        ms = genericTake (2*sz) $ mul (blastLE x) (blastLE y) [] ++ repeat False
        rs = genericTake (2*sz) $ [(i `elem` red) |  i <- [0 .. foldr max 0 red] ] ++ repeat False
        sz = 8 :: Integer
        mul _  []     ps = ps
        mul as (b:bs) ps = mul (False:as) bs (ites b (as `addPoly` ps) ps)


-- | Compute modulus/remainder of polynomials on bit-vectors.
mdp :: [Bool] -> [Bool] -> ([Bool], [Bool])
mdp xs ys = go (length ys - 1) (reverse ys)
  where degTop  = degree xs
        go _ []     = error "SBV.Polynomial.mdp: Impossible happened; exhausted ys before hitting 0"
        go n (b:bs)
         | n == 0   = (reverse qs, rs)
         | True     = let (rqs, rrs) = go (n-1) bs
                      in (ites b (reverse qs) rqs, ites b rs rrs)
         where degQuot = degTop - n
               ys' = replicate degQuot False ++ ys
               (qs, rs) = divx (degQuot+1) degTop xs ys'

degree :: [Bool] -> Int
degree xs = walk (length xs - 1) $ reverse xs
  where walk n []     = n
        walk n (b:bs) = if b then n else walk (n-1) bs

idx :: [Bool] -> Int -> Bool
idx []     _ = False
idx (x:_)  0 = x
idx (_:xs) i = idx xs (i-1)

divx :: Int -> Int -> [Bool] -> [Bool] -> ([Bool], [Bool])
divx n _ xs _ | n <= 0 = ([], xs)
divx n i xs ys'        = (q:qs, rs)
  where q        = xs `idx` i
        xs'      = ites q (xs `addPoly` ys') xs
        (qs, rs) = divx (n-1) (i-1) xs' (tail ys')

ites :: Bool -> [Bool] -> [Bool] -> [Bool]
ites s xs ys = if s then xs else ys

-- | Add two polynomials
addPoly :: [Bool] -> [Bool] -> [Bool]
addPoly xs    []      = xs
addPoly []    ys      = ys
addPoly (x:xs) (y:ys) = (x `xor` y) : addPoly xs ys


-- | Multiplication in GF(2^8). This is simple polynomial multiplication, followed
-- by the irreducible polynomial @x^8+x^4+x^3+x^1+1@. We simply use the 'pMult'
-- function exported by SBV to do the operation.
gf28Mult :: GF28 -> GF28 -> GF28
gf28Mult x y = pMult x y [8, 4, 3, 1, 0]

-- | Exponentiation by a constant in GF(2^8). The implementation uses the usual
-- square-and-multiply trick to speed up the computation.
gf28Pow :: GF28 -> Int -> GF28
gf28Pow n = pow
  where sq x  = x `gf28Mult` x
        pow 0    = 1
        pow i
         | odd i = n `gf28Mult` sq (pow (i `shiftR` 1))
         | True  = sq (pow (i `shiftR` 1))

-- | Computing inverses in GF(2^8). By the mathematical properties of GF(2^8)
-- and the particular irreducible polynomial used @x^8+x^5+x^3+x^1+1@, it
-- turns out that raising to the 254 power gives us the multiplicative inverse.
-- Of course, we can prove this using SBV:
--
-- >>> prove $ \x -> x ./= 0 .=> x `gf28Mult` gf28Inverse x .== 1
-- Q.E.D.
--
-- Note that we exclude @0@ in our theorem, as it does not have a
-- multiplicative inverse.
gf28Inverse :: GF28 -> GF28
gf28Inverse x = x `gf28Pow` 254

-----------------------------------------------------------------------------
-- * Implementing AES
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** Types and basic operations
-----------------------------------------------------------------------------
-- | AES state. The state consists of four 32-bit words, each of which is in turn treated
-- as four GF28's, i.e., 4 bytes. The T-Box implementation keeps the four-bytes together
-- for efficient representation.
type State = [Word32]

-- | The key, which can be 128, 192, or 256 bits. Represented as a sequence of 32-bit words.
type Key = [Word32]

-- | The key schedule. AES executes in rounds, and it treats first and last round keys slightly
-- differently than the middle ones. We reflect that choice by being explicit about it in our type.
-- The length of the middle list of keys depends on the key-size, which in turn determines
-- the number of rounds.
type KS = (Key, [Key], Key)

-- | Rotating a state row by a fixed amount to the right.
rotR :: [GF28] -> Int -> [GF28]
rotR [a, b, c, d] 1 = [d, a, b, c]
rotR [a, b, c, d] 2 = [c, d, a, b]
rotR [a, b, c, d] 3 = [b, c, d, a]
rotR xs           i = error $ "rotR: Unexpected input: " ++ show (xs, i)


toBytes :: Word32 -> [Word8]
toBytes w = [b0,b1,b2,b3]
  where
  b0 = fromIntegral (w `shiftR` 24)
  b1 = fromIntegral (w `shiftR` 16)
  b2 = fromIntegral (w `shiftR`  8)
  b3 = fromIntegral  w

fromBytes :: [Word8] -> Word32
fromBytes [b0,b1,b2,b3] = w
  where
  w = ((fromIntegral b0) `shiftL` 24) .|.
      ((fromIntegral b1) `shiftL` 16) .|.
      ((fromIntegral b2) `shiftL`  8) .|.
       (fromIntegral b3)
fromBytes bs = error ("Unexpected list length in fromBytes: " ++ show (length bs))


-----------------------------------------------------------------------------
-- ** The key schedule
-----------------------------------------------------------------------------

-- | Definition of round-constants, as specified in Section 5.2 of the AES standard.
roundConstants :: [GF28]
roundConstants = 0 : [ gf28Pow 2 (k-1) | k <- [1 .. ] ]

-- | The @InvMixColumns@ transformation, as described in Section 5.3.3 of the standard. Note
-- that this transformation is only used explicitly during key-expansion in the T-Box implementation
-- of AES.
invMixColumns :: State -> State
invMixColumns state = map fromBytes $ transpose $ mmult (map toBytes state)
 where dot f   = foldr1 xor . zipWith ($) f
       mmult :: [[Word8]] -> [[Word8]]
       mmult n = [map (dot r) n | r <- [ [mE, mB, mD, m9]
                                       , [m9, mE, mB, mD]
                                       , [mD, m9, mE, mB]
                                       , [mB, mD, m9, mE]
                                       ]]
       -- table-lookup versions of gf28Mult with the constants used in invMixColumns
       mE i = mETable !! fromIntegral i
       mB i = mBTable !! fromIntegral i
       mD i = mDTable !! fromIntegral i
       m9 i = m9Table !! fromIntegral i

mETable :: [GF28]
mETable = map (gf28Mult 0xE) [0..255]

mBTable :: [GF28]
mBTable = map (gf28Mult 0xB) [0..255]

mDTable :: [GF28]
mDTable = map (gf28Mult 0xD) [0..255]

m9Table :: [GF28]
m9Table = map (gf28Mult 0x9) [0..255]

-- | Key expansion. Starting with the given key, returns an infinite sequence of
-- words, as described by the AES standard, Section 5.2, Figure 11.
keyExpansion :: Integer -> Key -> [Key]
keyExpansion nk key = chop4 (keyExpansionWords nk key)
   where chop4 :: [a] -> [[a]]
         chop4 xs = let (f, r) = splitAt 4 xs in f : chop4 r

keyExpansionWords :: Integer -> Key -> [Word32]
keyExpansionWords nk key = keys
   where keys :: [Word32]
         keys = key ++ [nextWord i prev old | i <- [nk ..] | prev <- genericDrop (nk-1) keys | old <- keys]
         
         nextWord :: Integer -> Word32 -> Word32 -> Word32
         nextWord i prev old
           | i `mod` nk == 0           = old `xor` subWordRcon (prev `rotateL` 8) (roundConstants !! fromInteger (i `div` nk))
           | i `mod` nk == 4 && nk > 6 = old `xor` subWordRcon prev 0
           | True                      = old `xor` prev

         subWordRcon :: Word32 -> GF28 -> Word32
         subWordRcon w rc = fromBytes [a `xor` rc, b, c, d]
            where [a, b, c, d] = map sbox $ toBytes w


-----------------------------------------------------------------------------
-- ** The S-box transformation
-----------------------------------------------------------------------------

-- | The values of the AES S-box table. Note that we describe the S-box programmatically
-- using the mathematical construction given in Section 5.1.1 of the standard. However,
-- the code-generation will turn this into a mere look-up table, as it is just a
-- constant table, all computation being done at \"compile-time\".
sboxTable :: [GF28]
sboxTable = [xformByte (gf28Inverse b) | b <- [0 .. 255]]
  where xformByte :: GF28 -> GF28
        xformByte b = foldr xor 0x63 [b `rotateR` i | i <- [0, 4, 5, 6, 7]]

-- | The sbox transformation. We simply select from the sbox table. Note that we
-- are obliged to give a default value (here @0@) to be used if the index is out-of-bounds
-- as required by SBV's 'select' function. However, that will never happen since
-- the table has all 256 elements in it.
sbox :: GF28 -> GF28
sbox i = sboxTable !! fromIntegral i

-----------------------------------------------------------------------------
-- ** The inverse S-box transformation
-----------------------------------------------------------------------------

-- | The values of the inverse S-box table. Again, the construction is programmatic.
unSBoxTable :: [GF28]
unSBoxTable = [gf28Inverse (xformByte b) | b <- [0 .. 255]]
  where xformByte :: GF28 -> GF28
        xformByte b = foldr xor 0x05 [b `rotateR` i | i <- [2, 5, 7]]

-- | The inverse s-box transformation.
unSBox :: GF28 -> GF28
unSBox i = unSBoxTable !! fromIntegral i

-----------------------------------------------------------------------------
-- ** AddRoundKey transformation
-----------------------------------------------------------------------------

-- | Adding the round-key to the current state. We simply exploit the fact
-- that addition is just xor in implementing this transformation.
addRoundKey :: Key -> State -> State
addRoundKey = zipWith xor

-----------------------------------------------------------------------------
-- ** Tables for T-Box encryption
-----------------------------------------------------------------------------

-- | T-box table generation function for encryption
t0Func :: GF28 -> [GF28]
t0Func a = [s `gf28Mult` 2, s, s, s `gf28Mult` 3] where s = sbox a

-- | First look-up table used in encryption
t0 :: GF28 -> Word32
t0 i = t0Table !! fromIntegral i

t0Table :: [Word32]
t0Table = [fromBytes (t0Func a)          | a <- [0..255]]

-- | Second look-up table used in encryption
t1 :: GF28 -> Word32
t1 i = t1Table !! fromIntegral i

t1Table :: [Word32]
t1Table = [fromBytes (t0Func a `rotR` 1) | a <- [0..255]]

-- | Third look-up table used in encryption
t2 :: GF28 -> Word32
t2 i = t2Table !! fromIntegral i

t2Table :: [Word32]
t2Table = [fromBytes (t0Func a `rotR` 2) | a <- [0..255]]

-- | Fourth look-up table used in encryption
t3 :: GF28 -> Word32
t3 i = t3Table !! fromIntegral i

t3Table :: [Word32]
t3Table = [fromBytes (t0Func a `rotR` 3) | a <- [0..255]]

-----------------------------------------------------------------------------
-- ** Tables for T-Box decryption
-----------------------------------------------------------------------------

-- | T-box table generating function for decryption
u0Func :: GF28 -> [GF28]
u0Func a = [s `gf28Mult` 0xE, s `gf28Mult` 0x9, s `gf28Mult` 0xD, s `gf28Mult` 0xB] where s = unSBox a

-- | First look-up table used in decryption
u0 :: GF28 -> Word32
u0 i = u0Table !! fromIntegral i


u0Table :: [Word32]
u0Table = [fromBytes (u0Func a)          | a <- [0..255]]

-- | Second look-up table used in decryption
u1 :: GF28 -> Word32
u1 i = u1Table !! fromIntegral i

u1Table :: [Word32]
u1Table = [fromBytes (u0Func a `rotR` 1) | a <- [0..255]]

-- | Third look-up table used in decryption
u2 :: GF28 -> Word32
u2 i = u2Table !! fromIntegral i

u2Table :: [Word32]
u2Table = [fromBytes (u0Func a `rotR` 2) | a <- [0..255]]

-- | Fourth look-up table used in decryption
u3 :: GF28 -> Word32
u3 i = u3Table !! fromIntegral i

u3Table :: [Word32]
u3Table = [fromBytes (u0Func a `rotR` 3) | a <- [0..255]]

-----------------------------------------------------------------------------
-- ** AES rounds
-----------------------------------------------------------------------------

-- | Generic round function. Given the function to perform one round, a key-schedule,
-- and a starting state, it performs the AES rounds.
doRounds :: (Bool -> State -> Key -> State) -> KS -> State -> State
doRounds rnd (ikey, rkeys, fkey) sIn = rnd True (last rs) fkey
  where s0 = ikey `addRoundKey` sIn
        rs = s0 : [rnd False s k | s <- rs | k <- rkeys ]

-- | One encryption round. The first argument indicates whether this is the final round
-- or not, in which case the construction is slightly different.
aesRound :: Bool -> State -> Key -> State
aesRound isFinal s key = d `addRoundKey` key
  where d = map (f isFinal) [0..3]
        a = map toBytes s
        f True j = fromBytes [ sbox (a !! ((j+0) `mod` 4) !! 0)
                             , sbox (a !! ((j+1) `mod` 4) !! 1)
                             , sbox (a !! ((j+2) `mod` 4) !! 2)
                             , sbox (a !! ((j+3) `mod` 4) !! 3)
                             ]
        f False j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = t0 (a !! ((j+0) `mod` 4) !! 0)
                    e1 = t1 (a !! ((j+1) `mod` 4) !! 1)
                    e2 = t2 (a !! ((j+2) `mod` 4) !! 2)
                    e3 = t3 (a !! ((j+3) `mod` 4) !! 3)

-- | One decryption round. Similar to the encryption round, the first argument
-- indicates whether this is the final round or not.
aesInvRound :: Bool -> State -> Key -> State
aesInvRound isFinal s key = d `addRoundKey` key
  where d = map (f isFinal) [0..3]
        a = map toBytes s
        f True j = fromBytes [ unSBox (a !! ((j+0) `mod` 4) !! 0)
                             , unSBox (a !! ((j+3) `mod` 4) !! 1)
                             , unSBox (a !! ((j+2) `mod` 4) !! 2)
                             , unSBox (a !! ((j+1) `mod` 4) !! 3)
                             ]
        f False j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = u0 (a !! ((j+0) `mod` 4) !! 0)
                    e1 = u1 (a !! ((j+3) `mod` 4) !! 1)
                    e2 = u2 (a !! ((j+2) `mod` 4) !! 2)
                    e3 = u3 (a !! ((j+1) `mod` 4) !! 3)

-----------------------------------------------------------------------------
-- * AES API
-----------------------------------------------------------------------------

-- | Key schedule. Given a 128, 192, or 256 bit key, expand it to get key-schedules
-- for encryption and decryption. The key is given as a sequence of 32-bit words.
-- (4 elements for 128-bits, 6 for 192, and 8 for 256.)
aesKeySchedule :: Key -> (KS, KS)
aesKeySchedule key
  | nk `elem` [4, 6, 8]
  = (encKS, decKS)
  | True
  = error "aesKeySchedule: Invalid key size"
  where nk = genericLength key
        nr = nk + 6
        encKS@(f, m, l) = (head rKeys, genericTake (nr-1) (tail rKeys), rKeys !! fromInteger nr)
        decKS = (l, map invMixColumns (reverse m), f)
        rKeys = keyExpansion nk key

-- | Block encryption. The first argument is the plain-text, which must have
-- precisely 4 elements, for a total of 128-bits of input. The second
-- argument is the key-schedule to be used, obtained by a call to 'aesKeySchedule'.
-- The output will always have 4 32-bit words, which is the cipher-text.
aesEncrypt :: [Word32] -> KS -> [Word32]
aesEncrypt pt encKS
  | length pt == 4
  = doRounds aesRound encKS pt
  | True
  = error "aesEncrypt: Invalid plain-text size"

-- | Block decryption. The arguments are the same as in 'aesEncrypt', except
-- the first argument is the cipher-text and the output is the corresponding
-- plain-text.
aesDecrypt :: [Word32] -> KS -> [Word32]
aesDecrypt ct decKS
  | length ct == 4
  = doRounds aesInvRound decKS ct
  | True
  = error "aesDecrypt: Invalid cipher-text size"

-----------------------------------------------------------------------------
-- * Test vectors
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** 128-bit enc/dec test
-----------------------------------------------------------------------------

-- | 128-bit encryption test, from Appendix C.1 of the AES standard:
--
-- >>> map hex8 t128Enc
-- ["69c4e0d8","6a7b0430","d8cdb780","70b4c55a"]
--
t128Enc :: [Word32]
t128Enc = aesEncrypt pt ks
  where pt  = [0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff]
        key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f]
        (ks, _) = aesKeySchedule key

-- | 128-bit decryption test, from Appendix C.1 of the AES standard:
--
-- >>> map hex8 t128Dec
-- ["00112233","44556677","8899aabb","ccddeeff"]
--
t128Dec :: [Word32]
t128Dec = aesDecrypt ct ks
  where ct  = [0x69c4e0d8, 0x6a7b0430, 0xd8cdb780, 0x70b4c55a]
        key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f]
        (_, ks) = aesKeySchedule key

-----------------------------------------------------------------------------
-- ** 192-bit enc/dec test
-----------------------------------------------------------------------------

-- | 192-bit encryption test, from Appendix C.2 of the AES standard:
--
-- >>> map hex8 t192Enc
-- ["dda97ca4","864cdfe0","6eaf70a0","ec0d7191"]
--
t192Enc :: [Word32]
t192Enc = aesEncrypt pt ks
  where pt  = [0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff]
        key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617]
        (ks, _) = aesKeySchedule key

-- | 192-bit decryption test, from Appendix C.2 of the AES standard:
--
-- >>> map hex8 t192Dec
-- ["00112233","44556677","8899aabb","ccddeeff"]
--
t192Dec :: [Word32]
t192Dec = aesDecrypt ct ks
  where ct  = [0xdda97ca4, 0x864cdfe0, 0x6eaf70a0, 0xec0d7191]
        key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617]
        (_, ks) = aesKeySchedule key

-----------------------------------------------------------------------------
-- ** 256-bit enc/dec test
-----------------------------------------------------------------------------

-- | 256-bit encryption, from Appendix C.3 of the AES standard:
--
-- >>> map hex8 t256Enc
-- ["8ea2b7ca","516745bf","eafc4990","4b496089"]
--
t256Enc :: [Word32]
t256Enc = aesEncrypt pt ks
  where pt  = [0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff]
        key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f]
        (ks, _) = aesKeySchedule key

-- | 256-bit decryption, from Appendix C.3 of the AES standard:
--
-- >>> map hex8 t256Dec
-- ["00112233","44556677","8899aabb","ccddeeff"]
--
t256Dec :: [Word32]
t256Dec = aesDecrypt ct ks
  where ct  = [0x8ea2b7ca, 0x516745bf, 0xeafc4990, 0x4b496089]
        key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f, 0x10111213, 0x14151617, 0x18191a1b, 0x1c1d1e1f]
        (_, ks) = aesKeySchedule key


--------------------------------------------------------------------------------------------
-- | For doctest purposes only
hex8 :: (Show a, Integral a) => a -> String
hex8 v = replicate (8 - length s) '0' ++ s
  where s = flip showHex "" v

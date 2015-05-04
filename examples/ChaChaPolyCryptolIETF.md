% ChaCha20 and Poly1305 for IETF protocols 
% Y. Nir (Check Point),  A. Langley (Google Inc),  D. McNamee (Galois, Inc)
% July 28, 2014

## Abstract

This document defines the ChaCha20 stream cipher, as well as the use
of the Poly1305 authenticator, both as stand-alone algorithms, and as
a "combined mode", or Authenticated Encryption with Additional Data
(AEAD) algorithm.

This document does not introduce any new crypto, but is meant to
serve as a stable reference and an implementation guide.

This version of the document is a translation of the IETF draft document
draft-irtf-cfrg-chacha20-poly1305 into "literate Cryptol".
This document can be loaded and executed by a Cryptol interpreter.
There is an open source implementation of Cryptol available at http://cryptol.net

## Copyright Notice

Copyright (c) 2014 IETF Trust and the persons identified as the
document authors.  All rights reserved.

This document is subject to BCP 78 and the IETF Trust's Legal
Provisions Relating to IETF Documents
(http://trustee.ietf.org/license-info) in effect on the date of
publication of this document.  Please review these documents
carefully, as they describe your rights and restrictions with respect
to this document.

# Introduction

The Advanced Encryption Standard (AES - [FIPS-197]) has become the
gold standard in encryption.  Its efficient design, wide
implementation, and hardware support allow for high performance in
many areas.  On most modern platforms, AES is anywhere from 4x to 10x
as fast as the previous most-used cipher, 3-key Data Encryption
Standard (3DES - [FIPS-46]), which makes it not only the best choice,
but the only practical choice.

The problem is that if future advances in cryptanalysis reveal a
weakness in AES, users will be in an unenviable position.  With the
only other widely supported cipher being the much slower 3DES, it is
not feasible to re-configure implementations to use 3DES.
[standby-cipher] describes this issue and the need for a standby
cipher in greater detail.

This document defines such a standby cipher.  We use ChaCha20
([chacha]) with or without the Poly1305 ([poly1305]) authenticator.
These algorithms are not just fast.  They are fast even in software-
only C-language implementations, allowing for much quicker deployment
when compared with algorithms such as AES that are significantly
accelerated by hardware implementations.

This document does not introduce these new algorithms.  They have
been defined in scientific papers by D. J. Bernstein, which are
referenced by this document.  The purpose of this document is to
serve as a stable reference for IETF documents making use of these
algorithms.

These algorithms have undergone rigorous analysis.  Several papers
discuss the security of Salsa and ChaCha ([LatinDances],
[Zhenqing2012]).

## Conventions Used in This Document

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this
document are to be interpreted as described in [RFC2119].

The description of the ChaCha algorithm will at various time refer to
the ChaCha state as a "vector" or as a "matrix".  This follows the
use of these terms in DJB's paper.  The matrix notation is more
visually convenient, and gives a better notion as to why some rounds
are called "column rounds" while others are called "diagonal rounds".
Here's a diagram of how matrices relate to vectors (using the C
language convention of zero being the index origin).

```example
    0 , 1 ,  2 ,  3,
    4 , 5 ,  6 ,  7,
    8 , 9 ,  10,  11,
    12, 13,  14,  15
```

The elements in this vector or matrix are 32-bit unsigned integers.

```cryptol
module ChaCha20 where

type ChaChaState = [16][32]
```

The algorithm name is "ChaCha".  "ChaCha20" is a specific instance where
20 "rounds" (or 80 quarter rounds - see "The ChaCha Quarter Round", below)
are used.  Other variations are defined, with 8 or 12 rounds, but in this
document we only describe the 20-round ChaCha, so the names "ChaCha"
and "ChaCha20" will be used interchangeably.

# The Algorithms

The subsections below describe the algorithms used and the AEAD
construction.

## The ChaCha Quarter Round

The basic operation of the ChaCha algorithm is the quarter round.  It
operates on four 32-bit unsigned integers, denoted a, b, c, and d.
The operation is as follows:

```cryptol
ChaChaQuarterround : [4][32] -> [4][32]
ChaChaQuarterround [a, b, c, d] = [a'', b'', c'', d''] where
    a' = a + b
    d' = (d ^ a') <<< 16
    c' = c + d'
    b' = (b ^ c') <<< 12
    a'' = a' + b'
    d'' = (d' ^ a'') <<< 8
    c'' = c' + d''
    b'' = (b' ^ c'') <<< 7
```

Where "+" denotes integer addition without carry, "^" denotes a
bitwise XOR, and "<<< n" denotes an n-bit left rotation (towards the
high bits).

For example, let's see the add, XOR and roll operations from the
first two lines with sample numbers:

 *  b = 0x01020304
 *  a = 0x11111111
 *  d = 0x01234567
 *  a = a + b = 0x11111111 + 0x01020304 = 0x12131415
 *  d = d ^ a = 0x01234567 ^ 0x12131415 = 0x13305172
 *  d = d<<<16 = 0x51721330

### Test Vector for the ChaCha Quarter Round

For a test vector, we will use the same numbers as in the example,
adding something random for c.

After running a Quarter Round on these 4 numbers, we get these:

```cryptol
property ChaChaQuarterround_passes_test =
    ChaChaQuarterround [ 0x11111111 // a
                       , 0x01020304 // b
                       , 0x9b8d6f43 // c
                       , 0x01234567 // d
                       ]
    ==
                       [ 0xea2a92f4
                       , 0xcb1cf8ce
                       , 0x4581472e
                       , 0x5881c4bb
                       ]
```

## A Quarter Round on the ChaCha State

The ChaCha state does not have 4 integer numbers, but 16.  So the
quarter round operation works on only 4 of them - hence the name.
Each quarter round operates on 4 pre-determined numbers in the ChaCha
state.  We will denote by QUATERROUND(x,y,z,w) a quarter-round
operation on the numbers at indexes x, y, z, and w of the ChaCha
state when viewed as a vector.  For example, if we apply
QUARTERROUND(1,5,9,13) to a state, this means running the quarter
round operation on the elements marked with an asterisk, while
leaving the others alone:

```example
0   *a   2   3
4   *b   6   7
8   *c  10  11
12  *d  14  15
```

Note that this run of quarter round is part of what is called a
"column round". 

### Test Vector for the Quarter Round on the ChaCha state

For a test vector, we will use a ChaCha state that was generated
randomly:

Sample ChaCha State

```example
   879531e0  c5ecf37d  516461b1  c9a62f8a
   44c20ef3  3390af7f  d9fc690b  2a5f714c
   53372767  b00a5631  974c541a  359e9963
   5c971061  3d631689  2098d9d6  91dbd320
```
We will apply the QUARTERROUND(2,7,8,13) operation to this state.
For obvious reasons, this one is part of what is called a "diagonal
round":

After applying QUARTERROUND(2,7,8,13)

```example
   879531e0  c5ecf37d  bdb886dc  c9a62f8a
   44c20ef3  3390af7f  d9fc690b  cfacafd2
   e46bea80  b00a5631  974c541a  359e9963
   5c971061  ccc07c79  2098d9d6  91dbd320
```

Note that only the numbers in positions 2, 7, 8, and 13 changed.

In the Cryptol implementation of ChaCha20, the ChaChaQuarterround is called on four elements at a time, 
and there is no destructive state modification, so it would be artificial to reproduce the 
above example of the partially-destructively modified matrix. Instead, we show the output of
calling ChaChaQuarterround on the diagonal elements identified above:

```cryptol
property ChaChaQuarterround_passes_column_test =
    ChaChaQuarterround [ 0x516461b1 // a
                       , 0x2a5f714c // b
                       , 0x53372767 // c
                       , 0x3d631689 // d
                       ]
    ==
                       [ 0xbdb886dc
                       , 0xcfacafd2
                       , 0xe46bea80
                       , 0xccc07c79
                       ]
```

## The ChaCha20 block Function

The ChaCha block function transforms a ChaCha state by running
multiple quarter rounds.

The inputs to ChaCha20 are:

 * A 256-bit key, treated as a concatenation of 8 32-bit little-endian integers.
 * A 96-bit nonce, treated as a concatenation of 3 32-bit little-endian integers.
 * A 32-bit block count parameter, treated as a 32-bit little-endian integer.

The output is 64 random-looking bytes.

```cryptol
ChaCha20Block : ChaChaKey -> [96] -> [32] -> ChaChaState
```

The ChaCha algorithm described here uses a 256-bit key.  The original
algorithm also specified 128-bit keys and 8- and 12-round variants,
but these are out of scope for this document.  In this section we
describe the ChaCha block function.

```cryptol
type ChaChaKey = [256]
```

Note also that the original ChaCha had a 64-bit nonce and 64-bit
block count.  We have modified this here to be more consistent with
recommendations in section 3.2 of [RFC5116].  This limits the use of
a single (key,nonce) combination to 2^32 blocks, or 256 GB, but that
is enough for most uses.  In cases where a single key is used by
multiple senders, it is important to make sure that they don't use
the same nonces.  This can be assured by partitioning the nonce space
so that the first 32 bits are unique per sender, while the other 64
bits come from a counter.

The ChaCha20 state is initialized as follows:

 * The first 4 words (0-3) are constants: 0x61707865, 0x3320646e,
   0x79622d32, 0x6b206574.

```cryptol
FirstRow = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]
property FirstRow_correct = groupBy`{8}(join [ littleendian (split w)
                                             | w <- FirstRow ])
                            == "expand 32-byte k"
```

 * The next 8 words (4-11) are taken from the 256-bit key by
   reading the bytes in little-endian order, in 4-byte chunks.

```cryptol
KeyToRows : ChaChaKey -> [8][32]
KeyToRows key = [littleendian (split words) | words <- (split key)]
```

 * Word 12 is a block counter.  Since each block is 64-byte,
   a 32-bit word is enough for 256 Gigabytes of data.
 * Words 13-15 are a nonce, which should not be repeated for the same
   key.  The 13th word is the first 32 bits of the input nonce taken
   as a little-endian integer, while the 15th word is the last 32
   bits.

```verbatim
Initial state structure:

cccccccc  cccccccc  cccccccc  cccccccc
kkkkkkkk  kkkkkkkk  kkkkkkkk  kkkkkkkk
kkkkkkkk  kkkkkkkk  kkkkkkkk  kkkkkkkk
bbbbbbbb  nnnnnnnn  nnnnnnnn  nnnnnnnn

c=constant k=key b=blockcount n=nonce
```

```cryptol
NonceToRow : [96] -> [32] -> [4][32]
NonceToRow n i = [i] # [ littleendian (split words) | words <- groupBy`{32} n ]
```

```cryptol
BuildState : ChaChaKey -> [96] -> [32] -> [16][32]
BuildState key nonce i = split (join (FirstRow # KeyToRows key # NonceToRow nonce i))
```

ChaCha20 runs 20 rounds, alternating between "column" and "diagonal"
rounds.  Each round is 4 quarter-rounds, and they are run as follows.
Rounds 1-4 are part of the "column" round, while 5-8 are part of the
"diagonal" round:

```cryptol
columns = [ 0, 4, 8,  12,   // round 1 - column round
            1, 5, 9,  13,   // round 2
            2, 6, 10, 14,   // round 3
            3, 7, 11, 15 ]  // round 4
diags  = [ 0, 5, 10, 15,    // round 5 - diagonal round
           1, 6, 11, 12,    // round 6
           2, 7, 8,  13,    // round 7
           3, 4, 9,  14 ]   // round 8
```

The Cryptol pattern of using the `@@` operator on permutations of the indices of
the matrix creates a new matrix that consists of rows that correspond to the
quarter-round calls. To restore the element-indices to their original ordering,
after each application we perform the inverse permutation. Since the column
round is just a square matrix transposition, it inverts itself, but the
diagonal round needs to have an inverse permutation calculated, which we do
here:

```cryptol
inversePermutation (perms:[a+1]b) = [ indexOf i perms | i <- [ 0 .. a ] ]
invDiags = inversePermutation diags
invCols  = inversePermutation columns // which happens to be the same as columns

ChaChaTwoRounds (xs:ChaChaState) = xs'' where
    xs'  =  join [ChaChaQuarterround x | x <- groupBy`{4}(xs@@columns) ] @@ invCols
    xs'' = (join [ChaChaQuarterround x | x <- groupBy`{4}(xs'@@diags ) ]) @@ invDiags

ChaCha : ChaChaState -> [8] -> ChaChaState
ChaCha s n = chain@n where
    chain = [s] # [ ChaChaTwoRounds ci | ci <- chain | i <- [0 .. 9] ]
```

At the end of 20 rounds, the original input words are added to the
output words, and the result is serialized by sequencing the words
one-by-one in little-endian order.

```cryptol
// ChaCha20Block : ChaChaKey -> [96] -> [32] -> ChaChaState (repeated from above)
ChaCha20Block key nonce i = (ChaCha initialState 10) + initialState where
    initialState = BuildState key nonce i
```

### Test Vector for the ChaCha20 Block Function

For a test vector, we will use the following inputs to the ChaCha20
block function:

```cryptol
TestKey : ChaChaKey
TestKey = join (parseHexString
    ( "00:01:02:03:04:05:06:07:08:09:0a:0b:0c:0d:0e:0f:10:11:12:13:" #
      "14:15:16:17:18:19:1a:1b:1c:1d:1e:1f.") )
```

The key is a sequence of octets with no particular structure before we copy it
into the ChaCha state.

```cryptol
TestNonce : [96]
TestNonce = join (parseHexString "00:00:00:09:00:00:00:4a:00:00:00:00.")
```

After setting up the ChaCha state, it looks like this:

ChaCha State with the key set up.

```cryptol
TestState = BuildState TestKey TestNonce 1

property BuildState_correct = TestState == [
    0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
    0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c,
    0x00000001, 0x09000000, 0x4a000000, 0x00000000 ]
```

After running 20 rounds (10 column rounds interleaved with 10
diagonal rounds), the ChaCha state looks like this:

ChaCha State after 20 rounds

```cryptol
ChaCha20_state1 = [
    0x837778ab, 0xe238d763,  0xa67ae21e,  0x5950bb2f,
    0xc4f2d0c7, 0xfc62bb2f,  0x8fa018fc,  0x3f5ec7b7,
    0x335271c2, 0xf29489f3,  0xeabda8fc,  0x82e46ebd,
    0xd19c12b4, 0xb04e16de,  0x9e83d0cb,  0x4e3c50a2
    ]

property ChaChaStateAfter20_correct = ChaCha TestState 10 == ChaCha20_state1
```

Finally we add the original state to the result (simple vector or
matrix addition), giving this:

ChaCha State at the end of the ChaCha20 operation

```cryptol
ChaCha20_block_1 = [
    0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3,
    0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3,
    0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9,
    0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2
    ]

property ChaCha20_test1 = ChaCha20Block TestKey TestNonce 1 == ChaCha20_block_1
```

## The ChaCha20 encryption algorithm

ChaCha20 is a stream cipher designed by D. J. Bernstein.  It is a
refinement of the Salsa20 algorithm, and uses a 256-bit key.

ChaCha20 successively calls the ChaCha20 block function, with the
same key and nonce, and with successively increasing block counter
parameters.  ChaCha20 then serializes the resulting state by writing
the numbers in little-endian order, creating a key-stream block.
Concatenating the key-stream blocks from the successive blocks forms
a key stream, which is then XOR-ed with the plaintext.
Alternatively, each key-stream block can be XOR-ed with a plaintext
block before proceeding to create the next block, saving some memory.

There is no requirement for the plaintext to be an integral multiple
of 512-bits.  If there is extra keystream from the last block, it is
discarded.  Specific protocols MAY require that the plaintext and
ciphertext have certain length.  Such protocols need to specify how
the plaintext is padded, and how much padding it receives.

The inputs to ChaCha20 are:

 *   A 256-bit key
 *   A 32-bit initial counter.  This can be set to any number, but will
     usually be zero or one.  It makes sense to use 1 if we use the
     zero block for something else, such as generating a one-time
     authenticator key as part of an AEAD algorithm.
 *   A 96-bit nonce.  In some protocols, this is known as the
     Initialization Vector.
 *   an arbitrary-length plaintext

The output is an encrypted message of the same length.

```cryptol
// TODO: reorder args below, and get rid of this wrapper
ChaCha20Encrypt : {a} (fin a) => ChaChaKey -> [32] -> [96] -> [a][8] -> [a][8]
ChaCha20Encrypt k i n msg = ChaCha20EncryptBytes msg k n i

ChaCha20EncryptBytes msg k n i= [ m ^ kb | m <- msg | kb <- keystream ] where
    keystream = groupBy`{8}(join (join (ChaCha20ExpandKey k n i)))

ChaCha20ExpandKey : ChaChaKey -> [96] -> [32] -> [inf]ChaChaState
ChaCha20ExpandKey k n i = [ ToLittleEndian (ChaCha20Block k n j)
                          | j <- ([i ...]:[_][32])
                          ]

```

Decryption is done in the same way.  The ChaCha20 block function is
used to expand the key into a key stream, which is XOR-ed with the
ciphertext giving back the plaintext.

```cryptol
ChaCha20DecryptBytes = ChaCha20EncryptBytes
```

### Example and Test Vector for the ChaCha20 Cipher

For a test vector, we will use the following inputs to the ChaCha20
block function:

```cryptol
Sunscreen_Key = join (parseHexString
    ( "00:01:02:03:04:05:06:07:08:09:0a:0b:0c:0d:0e:0f:10:11:12:13:"
    # "14:15:16:17:18:19:1a:1b:1c:1d:1e:1f."
    ) )

Sunscreen_Nonce = join (parseHexString "00:00:00:00:00:00:00:4a:00:00:00:00.")
Sunscreen_Initial_Counter = 1
```

We use the following for the plaintext.  It was chosen to be long
enough to require more than one block, but not so long that it would
make this example cumbersome (so, less than 3 blocks):

Plaintext Sunscreen:

```cryptol
Plaintext_Sunscreen = "Ladies and Gentlemen of the class of '99: " #
                      "If I could offer you only one tip for the " #
                      "future, sunscreen would be it."
```

The following figure shows 4 ChaCha state matrices:

 1.  First block as it is set up.
 1.  Second block as it is set up.  Note that these blocks are only
        two bits apart - only the counter in position 12 is different.
 1.  Third block is the first block after the ChaCha20 block
        operation.
 1.  Final block is the second block after the ChaCha20 block
        operation was applied.

After that, we show the keystream.

First block setup:

```cryptol
Sunscreen_State1 = [
    0x61707865,  0x3320646e,  0x79622d32,  0x6b206574,
    0x03020100,  0x07060504,  0x0b0a0908,  0x0f0e0d0c,
    0x13121110,  0x17161514,  0x1b1a1918,  0x1f1e1d1c,
    0x00000001,  0x00000000,  0x4a000000,  0x00000000
    ]

property SunscreenBuildState_correct =
    BuildState Sunscreen_Key Sunscreen_Nonce 1 == Sunscreen_State1
```

Second block setup:

```cryptol
Sunscreen_State2 = [
    0x61707865,  0x3320646e,  0x79622d32,  0x6b206574,
    0x03020100,  0x07060504,  0x0b0a0908,  0x0f0e0d0c,
    0x13121110,  0x17161514,  0x1b1a1918,  0x1f1e1d1c,
    0x00000002,  0x00000000,  0x4a000000,  0x00000000
    ]

property SunscreenBuildState2_correct =
    BuildState Sunscreen_Key Sunscreen_Nonce 2 == Sunscreen_State2
```

First block after block operation:

```cryptol
SunscreenAfterBlock1 = [
    0xf3514f22, 0xe1d91b40, 0x6f27de2f, 0xed1d63b8,
    0x821f138c, 0xe2062c3d, 0xecca4f7e, 0x78cff39e,
    0xa30a3b8a, 0x920a6072, 0xcd7479b5, 0x34932bed,
    0x40ba4c79, 0xcd343ec6, 0x4c2c21ea, 0xb7417df0
    ]

property SunscreenBlock1_correct =
    ChaCha20Block Sunscreen_Key Sunscreen_Nonce 1 == SunscreenAfterBlock1
```

Second block after block operation:

```cryptol
SunscreenAfterBlock2 = [
    0x9f74a669, 0x410f633f, 0x28feca22, 0x7ec44dec,
    0x6d34d426, 0x738cb970, 0x3ac5e9f3, 0x45590cc4,
    0xda6e8b39, 0x892c831a, 0xcdea67c1, 0x2b7e1d90,
    0x037463f3, 0xa11a2073, 0xe8bcfb88, 0xedc49139
    ]

property SunscreenBlock2_correct =
    ChaCha20Block Sunscreen_Key Sunscreen_Nonce 2 == SunscreenAfterBlock2
```

Keystream:

```cryptol
SunscreenKeystream = (parseHexString
    ( "22:4f:51:f3:40:1b:d9:e1:2f:de:27:6f:b8:63:1d:ed:8c:13:1f:82:3d:2c:06:"
    # "e2:7e:4f:ca:ec:9e:f3:cf:78:8a:3b:0a:a3:72:60:0a:92:b5:79:74:cd:ed:2b:"
    # "93:34:79:4c:ba:40:c6:3e:34:cd:ea:21:2c:4c:f0:7d:41:b7:69:a6:74:9f:3f:"
    # "63:0f:41:22:ca:fe:28:ec:4d:c4:7e:26:d4:34:6d:70:b9:8c:73:f3:e9:c5:3a:"
    # "c4:0c:59:45:39:8b:6e:da:1a:83:2c:89:c1:67:ea:cd:90:1d:7e:2b:f3:63."
    ) )

SunscreenKeystream_correct (skref:[skwidth][8]) =
    take`{skwidth}
        (groupBy`{8} (join (join(ChaCha20ExpandKey
                                    Sunscreen_Key Sunscreen_Nonce 1)))) == skref
```

Finally, we XOR the Keystream with the plaintext, yielding the Ciphertext:

```cryptol
Ciphertext_Sunscreen =
    [0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80, 0x41, 0xba, 0x07,
     0x28, 0xdd, 0x0d, 0x69, 0x81, 0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43,
     0x60, 0xc2, 0x0a, 0x27, 0xaf, 0xcc, 0xfd, 0x9f, 0xae, 0x0b, 0xf9,
     0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33, 0xab, 0x8f, 0x59, 0x3d, 0xab,
     0xcd, 0x62, 0xb3, 0x57, 0x16, 0x39, 0xd6, 0x24, 0xe6, 0x51, 0x52,
     0xab, 0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8, 0x07, 0xca,
     0x0d, 0xbf, 0x50, 0x0d, 0x6a, 0x61, 0x56, 0xa3, 0x8e, 0x08, 0x8a,
     0x22, 0xb6, 0x5e, 0x52, 0xbc, 0x51, 0x4d, 0x16, 0xcc, 0xf8, 0x06,
     0x81, 0x8c, 0xe9, 0x1a, 0xb7, 0x79, 0x37, 0x36, 0x5a, 0xf9, 0x0b,
     0xbf, 0x74, 0xa3, 0x5b, 0xe6, 0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78,
     0x5e, 0x42, 0x87, 0x4d]

property ChaCha_encrypt_sunscreen_correct =
    ChaCha20EncryptBytes Plaintext_Sunscreen Sunscreen_Key Sunscreen_Nonce 1
    == Ciphertext_Sunscreen

property Sunscreen_decrypt_correct =
    ChaCha20DecryptBytes Ciphertext_Sunscreen Sunscreen_Key Sunscreen_Nonce 1
    == Plaintext_Sunscreen
```

# The Poly1305 algorithm

Poly1305 is a one-time authenticator designed by D. J. Bernstein.
Poly1305 takes a 32-byte one-time key and a message and produces a
16-byte tag.

The original article ([poly1305]) is entitled "The Poly1305-AES
message-authentication code", and the MAC function there requires a
128-bit AES key, a 128-bit "additional key", and a 128-bit (non-
secret) nonce.  AES is used there for encrypting the nonce, so as to
get a unique (and secret) 128-bit string, but as the paper states,
"There is nothing special about AES here.  One can replace AES with
an arbitrary keyed function from an arbitrary set of nonces to 16-
byte strings."

Regardless of how the key is generated, the key is partitioned into
two parts, called "r" and "s".  The pair ``(r,s)`` should be unique, and
MUST be unpredictable for each invocation (that is why it was
originally obtained by encrypting a nonce), while "r" MAY be
constant, but needs to be modified as follows before being used: ("r"
is treated as a 16-octet little-endian number):

 *  r[3], r[7], r[11], and r[15] are required to have their top four
    bits clear (be smaller than 16)

```cryptol
Om = 15 // odd masks - for 3, 7, 11 & 15
```
 *  r[4], r[8], and r[12] are required to have their bottom two bits
    clear (be divisible by 4)

The following Cryptol code clamps "r" to be appropriate:

```cryptol
Em = 252 // even masks - for 4, 8 & 12
nm = 255 // no mask

PolyMasks : [16][8]            // mask indices
PolyMasks = [ nm, nm, nm, Om,  // 0-3
              Em, nm, nm, Om,  // 4-7
              Em, nm, nm, Om,  // 8-11
              Em, nm, nm, Om ] // 12-15

Poly1305_clamp : [16][8] -> [16][8]
Poly1305_clamp r = [ re && mask | re <- r | mask <- PolyMasks ]
```

The "s" should be unpredictable, but it is perfectly acceptable to
generate both "r" and "s" uniquely each time.  Because each of them
is 128-bit, pseudo-randomly generating them (see "Generating the
Poly1305 key using ChaCha20") is also acceptable.

The inputs to Poly1305 are:

 *  A 256-bit one-time key
 *  An arbitrary length message (comprised of `floorBlocks` 16-byte blocks,
    and `rem` bytes left over)

The output is a 128-bit tag.

```cryptol
Poly1305 : {m, floorBlocks, rem} (fin m, floorBlocks == m/16, rem == m - floorBlocks*16) 
           => [256] -> [m][8] -> [16][8]
```

Set the constant prime "P" be 2^130-5.

```cryptol
P : [136]
P = 2^^130 - 5
```

First, the "r" value should be clamped.

```cryptol
Poly1305 key msg = result where
    [ru, su] = split key
    r : [136] // internal arithmetic on (128+8)-bit numbers
    r = littleendian ((Poly1305_clamp (split ru)) # [0x00])
    s = littleendian ((split su) # [0x00])
```

Next, divide the message into 16-byte blocks. The last block might be shorter:

 * Read each block as a little-endian number.
 * Add one bit beyond the number of octets.  For a 16-byte block this
   is equivalent to adding 2^128 to the number.  For the shorter
   block it can be 2^120, 2^112, or any power of two that is evenly
   divisible by 8, all the way down to 2^8.

```cryptol
    // pad all the blocks uniformly (we'll handle the final block later)
    paddedBlocks = [ 0x01 # (littleendian block)
                   | block <- groupBy`{16}(msg # (zero:[inf][8])) ]
```
 * If the block is not 17 bytes long (the last block), then left-pad it with
   zeros.  This is meaningless if you're treating it them as numbers.

```cryptol
    lastBlock : [136]
    lastBlock = zero # 0x01 # (littleendian (drop`{16*floorBlocks} msg))
```

 *  Add the current block to the accumulator.
 *  Multiply by "r"
 *  Set the accumulator to the result modulo p.  To summarize: 
    ``accum[i+1] = ((accum[i]+block)*r) % p``.

```cryptol
    accum:[_][136]
    accum = [zero:[136]] # [ computeElt a b r P | a <- accum | b <- paddedBlocks ]
    //       ^ the accumulator starts at zero
```

 * If the block division leaves no remainder, the last value of the accumulator is good
   otherwise compute the special-case padded block, and compute the final value of the accumulator

```cryptol
    lastAccum : [136]
    lastAccum = if `rem == 0
                   then accum@`floorBlocks
                   else computeElt (accum@`floorBlocks) lastBlock r P
```

Finally, the value of the secret key "s" is added to the accumulator,
and the 128 least significant bits are serialized in little-endian
order to form the tag.

```cryptol
    result = reverse (groupBy`{8} (drop`{8}(lastAccum + s)))

// Compute ((a + b) * r ) % P being pedantic about bit-widths
computeElt : [136] -> [136] -> [136] -> [136] -> [136]
computeElt a b r p = (drop`{137}bigResult) where
    bigResult : [273]
    aPlusB : [137]
    aPlusB = (0b0#a) + (0b0#b)                        // make room for carry
    timesR : [273]
    timesR = ((zero:[136])#aPlusB) * ((zero:[137])#r) // [a]*[b]=[a+b]
    bigResult = timesR % ((zero:[137])#p)

```

### Poly1305 Example and Test Vector

For our example, we will dispense with generating the one-time key
using AES, and assume that we got the following keying material:

 * Key Material: 85:d6:be:78:57:55:6d:33:7f:44:52:fe:42:d5:06:a8:01:
   03:80:8a:fb:0d:b2:fd:4a:bf:f6:af:41:49:f5:1b

```cryptol
Poly1305TestKey = join (parseHexString 
    ( "85:d6:be:78:57:55:6d:33:7f:44:52:fe:42:d5:06:a8:01:"
    # "03:80:8a:fb:0d:b2:fd:4a:bf:f6:af:41:49:f5:1b."
    ) )
```

 * s as an octet string: 01:03:80:8a:fb:0d:b2:fd:4a:bf:f6:af:41:49:f5:1b
 * s as a 128-bit number: 1bf54941aff6bf4afdb20dfb8a800301

```cryptol
Poly1305Test_s = parseHexString
    "01:03:80:8a:fb:0d:b2:fd:4a:bf:f6:af:41:49:f5:1b."
Poly1305Test_sbits = join (reverse Poly1305Test_s)

property poly1306Sokay = Poly1305Test_sbits == 0x1bf54941aff6bf4afdb20dfb8a800301
```


```cryptol
Poly1305TestMessage = "Cryptographic Forum Research Group"
```

 * r before clamping: 85:d6:be:78:57:55:6d:33:7f:44:52:fe:42:d5:06:a8
 * Clamped r as a number: 806d5400e52447c036d555408bed685.

Since Poly1305 works in 16-byte chunks, the 34-byte message divides
into 3 blocks.  In the following calculation, "Acc" denotes the
accumulator and "Block" the current block:

Here we define a Cryptol function that returns all of the intermediate
values of the accumulator:

```cryptol
// TODO: refactor the Poly function in terms of this AccumBlocks
// challenge: doing so while maintaining the clean literate correspondence with the spec
AccumBlocks : {m, floorBlocks, rem} (fin m, floorBlocks == m/16, rem == m - floorBlocks*16) 
              => [256] -> [m][8] -> ([_][136], [136])

AccumBlocks key msg = (accum, lastAccum) where
    [ru, su] = split key
    r : [136] // internal arithmetic on (128+8)-bit numbers
    r = littleendian ((Poly1305_clamp (split ru)) # [0x00])
    s = littleendian ((split su) # [0x00])
    // pad all the blocks uniformly (we'll handle the final block later)
    paddedBlocks = [ 0x01 # (littleendian block)
                   | block <- groupBy`{16}(msg # (zero:[inf][8])) ]
    lastBlock : [136]
    lastBlock = zero # 0x01 # (littleendian (drop`{16*floorBlocks} msg))
    accum:[_][136]
    accum = [zero:[136]] # [ computeElt a b r P | a <- accum | b <- paddedBlocks ]
    //       ^ the accumulator starts at zero
    lastAccum : [136]
    lastAccum = if `rem == 0
                   then accum@`floorBlocks
                   else computeElt (accum@`floorBlocks) lastBlock r P

```

```example
Block #1

Acc = 00
Block = 6f4620636968706172676f7470797243
Block with 0x01 byte = 016f4620636968706172676f7470797243
Acc + block = 016f4620636968706172676f7470797243
(Acc+Block) * r =
    b83fe991ca66800489155dcd69e8426ba2779453994ac90ed284034da565ecf
Acc = ((Acc+Block)*r) % P = 2c88c77849d64ae9147ddeb88e69c83fc

Block #2

Acc = 2c88c77849d64ae9147ddeb88e69c83fc
Block = 6f7247206863726165736552206d7572
Block with 0x01 byte = 016f7247206863726165736552206d7572
Acc + block = 437febea505c820f2ad5150db0709f96e
(Acc+Block) * r =
    21dcc992d0c659ba4036f65bb7f88562ae59b32c2b3b8f7efc8b00f78e548a26
Acc = ((Acc+Block)*r) % P = 2d8adaf23b0337fa7cccfb4ea344b30de

Last Block

Acc = 2d8adaf23b0337fa7cccfb4ea344b30de
Block = 7075
Block with 0x01 byte = 017075
Acc + block = 2d8adaf23b0337fa7cccfb4ea344ca153
(Acc + Block) * r =
    16d8e08a0f3fe1de4fe4a15486aca7a270a29f1e6c849221e4a6798b8e45321f
((Acc + Block) * r) % P = 28d31b7caff946c77c8844335369d03a7
```

```cryptol
property polyBlocksOK = 
    (blocks @ 1 == 0x02c88c77849d64ae9147ddeb88e69c83fc) &&
    (blocks @ 2 == 0x02d8adaf23b0337fa7cccfb4ea344b30de) &&
    (lastBlock  == 0x028d31b7caff946c77c8844335369d03a7) where
        (blocks, lastBlock) = AccumBlocks Poly1305TestKey Poly1305TestMessage
```

Adding s we get this number, and serialize if to get the tag:

Acc + s = 2a927010caf8b2bc2c6365130c11d06a8

Tag: a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9
   
```cryptol
// Putting it all together and testing:

Poly1305TestTag = "a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9."

property Poly1305_passes_test = Poly1305 Poly1305TestKey Poly1305TestMessage ==
    parseHexString Poly1305TestTag
```

## Generating the Poly1305 key using ChaCha20

As said in the "Poly 1305 Algorithm" section, it is acceptable to generate
the one-time Poly1305 pseudo-randomly.  This section proposes such a method.

To generate such a key pair (r,s), we will use the ChaCha20 block
function described in Section 2.3.  This assumes that we have a 256-
bit session key for the MAC function, such as SK_ai and SK_ar in
IKEv2 ([RFC5996]), the integrity key in ESP and AH, or the
client_write_MAC_key and server_write_MAC_key in TLS.  Any document
that specifies the use of Poly1305 as a MAC algorithm for some
protocol must specify that 256 bits are allocated for the integrity
key.  Note that in the AEAD construction defined in Section 2.8, the
same key is used for encryption and key generation, so the use of
SK_a* or *_write_MAC_key is only for stand-alone Poly1305.

The method is to call the block function with the following
parameters:
   
 * The 256-bit session integrity key is used as the ChaCha20 key.
 * The block counter is set to zero.
 * The protocol will specify a 96-bit or 64-bit nonce.  This MUST be
   unique per invocation with the same key, so it MUST NOT be
   randomly generated.  A counter is a good way to implement this,
   but other methods, such as an LFSR are also acceptable.  ChaCha20
   as specified here requires a 96-bit nonce.  So if the provided
   nonce is only 64-bit, then the first 32 bits of the nonce will be
   set to a constant number.  This will usually be zero, but for
   protocols with multiple senders it may be different for each
   sender, but should be the same for all invocations of the function
   with the same key by a particular sender.

After running the block function, we have a 512-bit state.  We take
the first 256 bits or the serialized state, and use those as the one-
time Poly1305 key: The first 128 bits are clamped, and form "r",
while the next 128 bits become "s".  The other 256 bits are
discarded.

Note that while many protocols have provisions for a nonce for
encryption algorithms (often called Initialization Vectors, or IVs),
they usually don't have such a provision for the MAC function.  In
that case the per-invocation nonce will have to come from somewhere
else, such as a message counter.
   
### Poly1305 Key Generation Test Vector

For this example, we'll set:

```cryptol
PolyKeyTest = join (parseHexString (
    "80 81 82 83 84 85 86 87 88 89 8a 8b 8c 8d 8e 8f " #
    "90 91 92 93 94 95 96 97 98 99 9a 9b 9c 9d 9e 9f "
    ))

PolyNonceTest : [96]
PolyNonceTest = join (
    parseHexString ("00 00 00 00 00 01 02 03 04 05 06 07 "))
```

The ChaCha state set up with key, nonce, and block counter zero:

```cryptol
PolyBuildState_testVector = [
     0x61707865,  0x3320646e,  0x79622d32,  0x6b206574,
     0x83828180,  0x87868584,  0x8b8a8988,  0x8f8e8d8c,
     0x93929190,  0x97969594,  0x9b9a9998,  0x9f9e9d9c,
     0x00000000,  0x00000000,  0x03020100,  0x07060504 ]

property PolyBuildState_correct = BuildState PolyKeyTest PolyNonceTest 0
    == PolyBuildState_testVector
```

The ChaCha state after 20 rounds:

```cryptol
PolyChaChaState_testVector = [
     0x8ba0d58a,  0xcc815f90,  0x27405081,  0x7194b24a,
     0x37b633a8,  0xa50dfde3,  0xe2b8db08,  0x46a6d1fd,
     0x7da03782,  0x9183a233,  0x148ad271,  0xb46773d1,
     0x3cc1875a,  0x8607def1,  0xca5c3086,  0x7085eb87 ]
 
property PolyChaCha_correct = ChaCha20Block PolyKeyTest PolyNonceTest 0 ==
    PolyChaChaState_testVector
```

And that output is also the 32-byte one-time key used for Poly1305.

```cryptol
PolyOutput = join (parseHexString (
    "8a d5 a0 8b 90 5f 81 cc 81 50 40 27 4a b2 94 71 " #
    "a8 33 b6 37 e3 fd 0d a5 08 db b8 e2 fd d1 a6 46 "))

GeneratePolyKeyUsingChaCha k n i = join [littleendian (groupBy`{8}b) 
                                        | b <- take `{8}(ChaCha20Block k n i) ]

property Poly_passes_test = GeneratePolyKeyUsingChaCha PolyKeyTest PolyNonceTest 0 == PolyOutput
```

## A Pseudo-Random Function for ChaCha/Poly-1305 based Crypto Suites

Some protocols such as IKEv2([RFC5996]) require a Pseudo-Random
Function (PRF), mostly for key derivation.  In the IKEv2 definition,
a PRF is a function that accepts a variable-length key and a
variable-length input, and returns a fixed-length output.  This
section does not specify such a function.

Poly-1305 is an obvious choice, because MAC functions are often used
as PRFs.  However, Poly-1305 prohibits using the same key twice,
whereas the PRF in IKEv2 is used multiple times with the same key.
Adding a nonce or a counter to Poly-1305 can solve this issue, much
as we do when using this function as a MAC, but that would require
changing the interface for the PRF function.

Chacha20 could be used as a key-derivation function, by generating an
arbitrarily long keystream.  However, that is not what protocols such
as IKEv2 require.

For this reason, this document does not specify a PRF, and recommends
that crypto suites use some other PRF such as PRF_HMAC_SHA2_256
(section 2.1.2 of [RFC4868])

## AEAD Construction

AEAD_CHACHA20-POLY1305 is an authenticated encryption with additional
data algorithm.  The inputs to AEAD_CHACHA20-POLY1305 are:

 *  A 256-bit key
 *  A 96-bit nonce - different for each invocation with the same key.
 *  An arbitrary length plaintext (fewer than 2^64 bytes)
 *  Arbitrary length additional data (AAD) (fewer than 2^64 bytes)

```cryptol
AEAD_CHACHA20_POLY1305 : {m, n}
                         (fin m, 64 >= width m
                         ,fin n, 64 >= width n )
                       => [256] -> [96] -> [m][8] -> [n][8]
                       -> [m+16][8]

AEAD_CHACHA20_POLY1305 k nonce p aad = (ct # tag) where 
```

Some protocols may have unique per-invocation inputs that are not 96-
bit in length.  For example, IPsec may specify a 64-bit nonce.  In
such a case, it is up to the protocol document to define how to
transform the protocol nonce into a 96-bit nonce, for example by
concatenating a constant value.

The ChaCha20 and Poly1305 primitives are combined into an AEAD that
takes a 256-bit key and 96-bit nonce as follows:

 *  First, a Poly1305 one-time key is generated from the 256-bit key
    and nonce using the procedure described in "Generating the Poly1305 key using ChaCha20".

```cryptol
    PolyKey = GeneratePolyKeyUsingChaCha k nonce 0
```

 *  Next, the ChaCha20 encryption function is called to encrypt the
    plaintext, using the input key and nonce, and with the initial
    counter set to 1.

```cryptol
    ct = ChaCha20EncryptBytes p k nonce 1 
```

 *  Finally, the Poly1305 function is called with the Poly1305 key
    calculated above, and a message constructed as a concatenation of
    the following:
    *  The AAD
    *  padding1 - the padding is up to 15 zero bytes, and it brings
       the total length so far to an integral multiple of 16.  If the
       length of the AAD was already an integral multiple of 16 bytes,
       this field is zero-length.
    *  The ciphertext
    *  padding2 - the padding is up to 15 zero bytes, and it brings
       the total length so far to an integral multiple of 16.  If the
       length of the ciphertext was already an integral multiple of 16
       bytes, this field is zero-length.
    *  The length of the additional data in octets (as a 64-bit
       little-endian integer).
    *  The length of the ciphertext in octets (as a 64-bit little-
       endian integer).

```cryptol
    ptlen : [8][8]
    ptlen = groupBy`{8}(littleendian (groupBy`{8}(`m:[64]))) 
    adlen : [8][8]
    adlen = groupBy`{8}(littleendian (groupBy`{8}(`n:[64])))
    // compute padding
    tag = Poly1305 PolyKey (AeadConstruction aad ct)
	
//ct in this function has tag removed
AeadConstruction (AAD : [n][8]) (CT : [m][8]) = (AAD # padding1 # CT # padding2 # adlen # ptlen) where
	padding1 = (zero:[(16-n%16)][8])
	padding2 = (zero:[(16-m%16)][8])
	adlen : [8][8]
	adlen = groupBy`{8}(littleendian (groupBy`{8}(`n:[64])))
	ptlen : [8][8]
	ptlen = groupBy`{8}(littleendian (groupBy`{8}(`m:[64])))

```

The output from the AEAD is twofold:

 *  A ciphertext of the same length as the plaintext.
 *  A 128-bit tag, which is the output of the Poly1305 function.

Decryption is pretty much the same thing.

```cryptol
AEAD_CHACHA20_POLY1305_DECRYPT : {m, n} (fin m, fin n
                                 ,64 >= width m, 64 >= width n)
                                 => [256] -> [96]
                                    -> [m+16][8] -> [n][8]
                                    -> ([m][8], Bit)								
AEAD_CHACHA20_POLY1305_DECRYPT k nonce ct ad = (pt, valid) where
    inTag = drop`{m}ct
    inCt = take`{m}ct
    PolyKey = GeneratePolyKeyUsingChaCha k nonce 0
    pt = ChaCha20DecryptBytes inCt k nonce 1
    ptlen : [8][8]
    ptlen = groupBy`{8}(littleendian (groupBy`{8}(`m:[64])))
    adlen : [8][8]
    adlen = groupBy`{8}(littleendian (groupBy`{8}(`n:[64])))
    tag = Poly1305 PolyKey (AeadConstruction ad inCt)
    valid = tag == inTag
```

A few notes about this design:

 1.  The amount of encrypted data possible in a single invocation is
     2^32-1 blocks of 64 bytes each, because of the size of the block
     counter field in the ChaCha20 block function.  This gives a total
     of 247,877,906,880 bytes, or nearly 256 GB.  This should be
     enough for traffic protocols such as IPsec and TLS, but may be
     too small for file and/or disk encryption.  For such uses, we can
     return to the original design, reduce the nonce to 64 bits, and
     use the integer at position 13 as the top 32 bits of a 64-bit
     block counter, increasing the total message size to over a
     million petabytes (1,180,591,620,717,411,303,360 bytes to be
     exact).

 1.  Despite the previous item, the ciphertext length field in the
     construction of the buffer on which Poly1305 runs limits the
     ciphertext (and hence, the plaintext) size to 2^64 bytes, or
     sixteen thousand petabytes (18,446,744,073,709,551,616 bytes to
     be exact).

### Example and Test Vector for AEAD_CHACHA20-POLY1305

For a test vector, we will use the following inputs to the
AEAD_CHACHA20-POLY1305 function:

Plaintext:

```cryptol
AeadPt = "Ladies and Gentlemen of the class of '99: " #
         "If I could offer you only one tip for " #
         "the future, sunscreen would be it."

AeadAAD = parseHexString "50 51 52 53 c0 c1 c2 c3 c4 c5 c6 c7 "

AeadKey = join (parseHexString (
    "80 81 82 83 84 85 86 87 88 89 8a 8b 8c 8d 8e 8f " #
    "90 91 92 93 94 95 96 97 98 99 9a 9b 9c 9d 9e 9f " ))


AeadIV = join [ 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47 ]

AeadC = join [0x07, 0x00, 0x00, 0x00]

AeadNonce = AeadC # AeadIV
```

32-bit fixed-common part:

```cryptol
AeadCT = ChaCha20EncryptBytes AeadPt AeadKey AeadNonce 1

AeadPolyKey = GeneratePolyKeyUsingChaCha AeadKey (AeadC # AeadIV) 0

ADleLen : [8][8]
ADleLen = groupBy`{8}(littleendian (groupBy`{8}((width AeadAAD):[64])))

CTleLen : [8][8]
CTleLen = groupBy`{8}(littleendian (groupBy`{8}((width AeadCT):[64])))

AeadTag = Poly1305 AeadPolyKey (AeadConstruction AeadAAD AeadCT)
```

Set up for generating poly1305 one-time key (sender id=7):

```cryptol
AeadPolyOneTimeKey_testVector = [
    0x61707865,  0x3320646e,  0x79622d32,  0x6b206574,
    0x83828180,  0x87868584,  0x8b8a8988,  0x8f8e8d8c,
    0x93929190,  0x97969594,  0x9b9a9998,  0x9f9e9d9c,
    0x00000000,  0x00000007,  0x43424140,  0x47464544 ]

property AeadPolyKeyBuildState_correct = 
    BuildState AeadKey AeadNonce 0 == AeadPolyOneTimeKey_testVector
```

After generating Poly1305 one-time key:

```cryptol
AeadPolyOneTimeKeyState = [
    0x252bac7b,  0xaf47b42d,  0x557ab609,  0x8455e9a4,
    0x73d6e10a,  0xebd97510,  0x7875932a,  0xff53d53e,
    0xdecc7ea2,  0xb44ddbad,  0xe49c17d1,  0xd8430bc9,
    0x8c94b7bc,  0x8b7d4b4b,  0x3927f67d,  0x1669a432]

property AeadPolyChaCha_correct = 
    ChaCha20Block AeadKey AeadNonce 0 == AeadPolyOneTimeKeyState
```

Poly1305 Key:

```cryptol
Poly1305Key_testVector = join (parseHexString (
    "7b ac 2b 25 2d b4 47 af 09 b6 7a 55 a4 e9 55 84 " #
    "0a e1 d6 73 10 75 d9 eb 2a 93 75 78 3e d5 53 ff " ))

property poly1305Test_correct = AeadPolyKey == Poly1305Key_testVector

Poly1305_r = 0x0455e9a4057ab6080f47b42c052bac7b
Poly1305_s = 0xff53d53e7875932aebd9751073d6e10a
```

```verbatim
Keystream bytes:
9f:7b:e9:5d:01:fd:40:ba:15:e2:8f:fb:36:81:0a:ae:
c1:c0:88:3f:09:01:6e:de:dd:8a:d0:87:55:82:03:a5:
4e:9e:cb:38:ac:8e:5e:2b:b8:da:b2:0f:fa:db:52:e8:
75:04:b2:6e:be:69:6d:4f:60:a4:85:cf:11:b8:1b:59:
fc:b1:c4:5f:42:19:ee:ac:ec:6a:de:c3:4e:66:69:78:
8e:db:41:c4:9c:a3:01:e1:27:e0:ac:ab:3b:44:b9:cf:
5c:86:bb:95:e0:6b:0d:f2:90:1a:b6:45:e4:ab:e6:22:
15:38


Ciphertext:
000  d3 1a 8d 34 64 8e 60 db 7b 86 af bc 53 ef 7e c2|...4d.`.{...S.~.
016  a4 ad ed 51 29 6e 08 fe a9 e2 b5 a7 36 ee 62 d6|...Q)n......6.b.
032  3d be a4 5e 8c a9 67 12 82 fa fb 69 da 92 72 8b|=..^..g....i..r.
048  1a 71 de 0a 9e 06 0b 29 05 d6 a5 b6 7e cd 3b 36|.q.....)....~.;6
064  92 dd bd 7f 2d 77 8b 8c 98 03 ae e3 28 09 1b 58|...-w......(..X
080  fa b3 24 e4 fa d6 75 94 55 85 80 8b 48 31 d7 bc|..$...u.U...H1..
096  3f f4 de f0 8e 4b 7a 9d e5 76 d2 65 86 ce c6 4b|?....Kz..v.e...K
112  61 16                                          |a.
```

AEAD Construction for Poly1305:

```cryptol
AeadConstructionTestVector = parseHexString (
   "50:51:52:53:c0:c1:c2:c3:c4:c5:c6:c7:00:00:00:00:" #
   "d3:1a:8d:34:64:8e:60:db:7b:86:af:bc:53:ef:7e:c2:" #
   "a4:ad:ed:51:29:6e:08:fe:a9:e2:b5:a7:36:ee:62:d6:" #
   "3d:be:a4:5e:8c:a9:67:12:82:fa:fb:69:da:92:72:8b:" #
   "1a:71:de:0a:9e:06:0b:29:05:d6:a5:b6:7e:cd:3b:36:" #
   "92:dd:bd:7f:2d:77:8b:8c:98:03:ae:e3:28:09:1b:58:" #
   "fa:b3:24:e4:fa:d6:75:94:55:85:80:8b:48:31:d7:bc:" #
   "3f:f4:de:f0:8e:4b:7a:9d:e5:76:d2:65:86:ce:c6:4b:" #
   "61:16:00:00:00:00:00:00:00:00:00:00:00:00:00:00:" #
   "0c:00:00:00:00:00:00:00:72:00:00:00:00:00:00:00." )
```

Note the 4 zero bytes in line 000 and the 14 zero bytes in line 128

```cryptol
// Tag:
AeadTagTestVector = parseHexString "1a:e1:0b:59:4f:09:e2:6a:7e:90:2e:cb:d0:60:06:91."
```

```cryptol
property AeadTag_correct = AeadTag == AeadTagTestVector 

property AeadConstruction_correct = (AeadConstruction AeadAAD AeadCT) == AeadConstructionTestVector

property AeadDecrypt_correct = ptMatches && isValid where
    (pt,isValid) = AEAD_CHACHA20_POLY1305_DECRYPT AeadKey (AeadIV # AeadC) cypherText AeadAAD
    cypherText   = (AEAD_CHACHA20_POLY1305 AeadKey (AeadIV # AeadC) AeadPt AeadAAD)
    ptMatches    = AeadPt == pt

```

# Implementation Advice

Each block of ChaCha20 involves 16 move operations and one increment
operation for loading the state, 80 each of XOR, addition and Roll
operations for the rounds, 16 more add operations and 16 XOR
operations for protecting the plaintext.  Section 2.3 describes the
ChaCha block function as "adding the original input words".  This
implies that before starting the rounds on the ChaCha state, we copy
it aside, only to add it in later.  This is correct, but we can save
a few operations if we instead copy the state and do the work on the
copy.  This way, for the next block you don't need to recreate the
state, but only to increment the block counter.  This saves
approximately 5.5% of the cycles.

It is not recommended to use a generic big number library such as the
one in OpenSSL for the arithmetic operations in Poly1305.  Such
libraries use dynamic allocation to be able to handle any-sized
integer, but that flexibility comes at the expense of performance as
well as side-channel security.  More efficient implementations that
run in constant time are available, one of them in DJB's own library,
NaCl ([NaCl]).  A constant-time but not optimal approach would be to
naively implement the arithmetic operations for a 288-bit integers,
because even a naive implementation will not exceed 2^288 in the
multiplication of (acc+block) and r.  An efficient constant-time
implementation can be found in the public domain library poly1305-
donna ([poly1305_donna]).


# Security Considerations

The ChaCha20 cipher is designed to provide 256-bit security.

The Poly1305 authenticator is designed to ensure that forged messages
are rejected with a probability of 1-(n/(2^102)) for a 16n-byte
message, even after sending 2^64 legitimate messages, so it is SUF-
CMA in the terminology of [AE].

Proving the security of either of these is beyond the scope of this
document.  Such proofs are available in the referenced academic
papers.

The most important security consideration in implementing this draft
is the uniqueness of the nonce used in ChaCha20.  Counters and LFSRs
are both acceptable ways of generating unique nonces, as is
encrypting a counter using a 64-bit cipher such as DES.  Note that it
is not acceptable to use a truncation of a counter encrypted with a
128-bit or 256-bit cipher, because such a truncation may repeat after
a short time.

The Poly1305 key MUST be unpredictable to an attacker.  Randomly
generating the key would fulfill this requirement, except that
Poly1305 is often used in communications protocols, so the receiver
should know the key.  Pseudo-random number generation such as by
encrypting a counter is acceptable.  Using ChaCha with a secret key
and a nonce is also acceptable.

The algorithms presented here were designed to be easy to implement
in constant time to avoid side-channel vulnerabilities.  The
operations used in ChaCha20 are all additions, XORs, and fixed
rotations.  All of these can and should be implemented in constant
time.  Access to offsets into the ChaCha state and the number of
operations do not depend on any property of the key, eliminating the
chance of information about the key leaking through the timing of
cache misses.

For Poly1305, the operations are addition, multiplication and
modulus, all on >128-bit numbers.  This can be done in constant time,
but a naive implementation (such as using some generic big number
library) will not be constant time.  For example, if the
multiplication is performed as a separate operation from the modulus,
the result will some times be under 2^256 and some times be above
2^256.  Implementers should be careful about timing side-channels for
Poly1305 by using the appropriate implementation of these operations.


# IANA Considerations

There are no IANA considerations for this document.


# Acknowledgements

ChaCha20 and Poly1305 were invented by Daniel J. Bernstein.  The AEAD
construction and the method of creating the one-time poly1305 key
were invented by Adam Langley.

Thanks to Robert Ransom, Watson Ladd, Stefan Buhler, and kenny
patterson for their helpful comments and explanations.  Thanks to
Niels Moeller for suggesting the more efficient AEAD construction in
this document.  Special thanks to Ilari Liusvaara for providing extra
test vectors, helpful comments, and for being the first to attempt an
implementation from this draft.

# References

## Normative References

```example
[RFC2119]  Bradner, S., "Key words for use in RFCs to Indicate
          Requirement Levels", BCP 14, RFC 2119, March 1997.

[chacha]   Bernstein, D., "ChaCha, a variant of Salsa20", Jan 2008.

[poly1305]
          Bernstein, D., "The Poly1305-AES message-authentication
          code", Mar 2005.
```

## Informative References

```example
[AE]       Bellare, M. and C. Namprempre, "Authenticated Encryption:
          Relations among notions and analysis of the generic
          composition paradigm",
          <http://cseweb.ucsd.edu/~mihir/papers/oem.html>.

[FIPS-197]
          National Institute of Standards and Technology, "Advanced
          Encryption Standard (AES)", FIPS PUB 197, November 2001.

[FIPS-46]  National Institute of Standards and Technology, "Data
          Encryption Standard", FIPS PUB 46-2, December 1993,
          <http://www.itl.nist.gov/fipspubs/fip46-2.htm>.

[LatinDances]
          Aumasson, J., Fischer, S., Khazaei, S., Meier, W., and C.
          Rechberger, "New Features of Latin Dances: Analysis of
          Salsa, ChaCha, and Rumba", Dec 2007.

[NaCl]     Bernstein, D., Lange, T., and P. Schwabe, "NaCl:
          Networking and Cryptography library",
          <http://nacl.cace-project.eu/index.html>.

[RFC4868]  Kelly, S. and S. Frankel, "Using HMAC-SHA-256, HMAC-SHA-
          384, and HMAC-SHA-512 with IPsec", RFC 4868, May 2007.

[RFC5116]  McGrew, D., "An Interface and Algorithms for Authenticated
          Encryption", RFC 5116, January 2008.

[RFC5996]  Kaufman, C., Hoffman, P., Nir, Y., and P. Eronen,
          "Internet Key Exchange Protocol Version 2 (IKEv2)",
          RFC 5996, September 2010.

[Zhenqing2012]
          Zhenqing, S., Bin, Z., Dengguo, F., and W. Wenling,
          "Improved key recovery attacks on reduced-round salsa20
          and chacha", 2012.

[poly1305_donna]
          Floodyberry, A., "Poly1305-donna",
          <https://github.com/floodyberry/poly1305-donna>.

[standby-cipher]
          McGrew, D., Grieco, A., and Y. Sheffer, "Selection of
          Future Cryptographic Standards",
          draft-mcgrew-standby-cipher (work in progress).
```


Authors' Addresses

```verbatim
Yoav Nir
Check Point Software Technologies Ltd.
5 Hasolelim st.
Tel Aviv  6789735
Israel
Email: ynir.ietf@gmail.com

Adam Langley
Google Inc
Email: agl@google.com

Dylan McNamee
Galois Inc
Email: dylan@galois.com
```

# Appendix: Additional test vectors

## The ChaCha20 Block Functions

```cryptol
// helper macros for higher-up properties
TV_block_correct key nonce blockcounter result = ChaCha20Block key nonce blockcounter == result
	
TV_block_Keystream_correct key nonce blockcounter keystream =
	take`{0x40} (groupBy`{8} (join (join (ChaCha20ExpandKey key nonce blockcounter)))) == keystream

ChaCha20_block_correct key nonce blockcounter result keystream = 
	TV_block_correct key nonce blockcounter result && 
	TV_block_Keystream_correct key nonce blockcounter keystream
```

### Test Vector #1

```cryptol
TV1_block_Key = zero:ChaChaKey
TV1_block_Nonce = zero:[96]
TV1_block_BlockCounter = 0

TV1_block_After20 = [
    0xade0b876, 0x903df1a0, 0xe56a5d40, 0x28bd8653,
    0xb819d2bd, 0x1aed8da0, 0xccef36a8, 0xc70d778b,
    0x7c5941da, 0x8d485751, 0x3fe02477, 0x374ad8b8,
    0xf4b8436a, 0x1ca11815, 0x69b687c3, 0x8665eeb2]

TV1_block_KeyStream = [
    0x76, 0xb8, 0xe0, 0xad, 0xa0, 0xf1, 0x3d, 0x90, 0x40, 0x5d, 0x6a, 0xe5, 0x53, 0x86, 0xbd, 0x28,
    0xbd, 0xd2, 0x19, 0xb8, 0xa0, 0x8d, 0xed, 0x1a, 0xa8, 0x36, 0xef, 0xcc, 0x8b, 0x77, 0x0d, 0xc7,
    0xda, 0x41, 0x59, 0x7c, 0x51, 0x57, 0x48, 0x8d, 0x77, 0x24, 0xe0, 0x3f, 0xb8, 0xd8, 0x4a, 0x37,
    0x6a, 0x43, 0xb8, 0xf4, 0x15, 0x18, 0xa1, 0x1c, 0xc3, 0x87, 0xb6, 0x69, 0xb2, 0xee, 0x65, 0x86]

property TV1_block_correct = ChaCha20_block_correct TV1_block_Key TV1_block_Nonce TV1_block_BlockCounter TV1_block_After20 TV1_block_KeyStream

```
	
### Test Vector #2

```cryptol
TV2_block_Key = zero:ChaChaKey
TV2_block_Nonce = zero:[96]
TV2_block_BlockCounter = 1

TV2_block_After20 = [
	0xbee7079f, 0x7a385155, 0x7c97ba98, 0x0d082d73,
	0xa0290fcb, 0x6965e348, 0x3e53c612, 0xed7aee32,
	0x7621b729, 0x434ee69c, 0xb03371d5, 0xd539d874,
	0x281fed31, 0x45fb0a51, 0x1f0ae1ac, 0x6f4d794b]

TV2_block_KeyStream = [
	0x9f, 0x07, 0xe7, 0xbe, 0x55, 0x51, 0x38, 0x7a, 0x98, 0xba, 0x97, 0x7c, 0x73, 0x2d, 0x08, 0x0d,
	0xcb, 0x0f, 0x29, 0xa0, 0x48, 0xe3, 0x65, 0x69, 0x12, 0xc6, 0x53, 0x3e, 0x32, 0xee, 0x7a, 0xed,
	0x29, 0xb7, 0x21, 0x76, 0x9c, 0xe6, 0x4e, 0x43, 0xd5, 0x71, 0x33, 0xb0, 0x74, 0xd8, 0x39, 0xd5,
	0x31, 0xed, 0x1f, 0x28, 0x51, 0x0a, 0xfb, 0x45, 0xac, 0xe1, 0x0a, 0x1f, 0x4b, 0x79, 0x4d, 0x6f]

property TV2_block_correct = ChaCha20_block_correct TV2_block_Key TV2_block_Nonce TV2_block_BlockCounter TV2_block_After20 TV2_block_KeyStream

	
```

### Test Vector #3

```cryptol
TV3_block_Key = (zero # 0b1):ChaChaKey
TV3_block_Nonce = zero:[96]
TV3_block_BlockCounter = 1

TV3_block_After20 = [
	0x2452eb3a, 0x9249f8ec, 0x8d829d9b, 0xddd4ceb1,
	0xe8252083, 0x60818b01, 0xf38422b8, 0x5aaa49c9,
	0xbb00ca8e, 0xda3ba7b4, 0xc4b592d1, 0xfdf2732f,
	0x4436274e, 0x2561b3c8, 0xebdd4aa6, 0xa0136c00]
	
TV3_block_KeyStream = [
	0x3a, 0xeb, 0x52, 0x24, 0xec, 0xf8, 0x49, 0x92, 0x9b, 0x9d, 0x82, 0x8d, 0xb1, 0xce, 0xd4, 0xdd, 
	0x83, 0x20, 0x25, 0xe8, 0x01, 0x8b, 0x81, 0x60, 0xb8, 0x22, 0x84, 0xf3, 0xc9, 0x49, 0xaa, 0x5a, 
	0x8e, 0xca, 0x00, 0xbb, 0xb4, 0xa7, 0x3b, 0xda, 0xd1, 0x92, 0xb5, 0xc4, 0x2f, 0x73, 0xf2, 0xfd, 
	0x4e, 0x27, 0x36, 0x44, 0xc8, 0xb3, 0x61, 0x25, 0xa6, 0x4a, 0xdd, 0xeb, 0x00, 0x6c, 0x13, 0xa0]

property TV3_block_correct = ChaCha20_block_correct TV3_block_Key TV3_block_Nonce TV3_block_BlockCounter TV3_block_After20 TV3_block_KeyStream

```

### Test Vector #4

```cryptol
TV4_block_Key = ( 0x00ff # zero):ChaChaKey
TV4_block_Nonce = zero:[96]
TV4_block_BlockCounter = 2

TV4_block_After20 = [
	0xfb4dd572, 0x4bc42ef1, 0xdf922636, 0x327f1394,
	0xa78dea8f, 0x5e269039, 0xa1bebbc1, 0xcaf09aae,
	0xa25ab213, 0x48a6b46c, 0x1b9d9bcb, 0x092c5be6,
	0x546ca624, 0x1bec45d5, 0x87f47473, 0x96f0992e]
	
TV4_block_KeyStream = [
	0x72, 0xd5, 0x4d, 0xfb, 0xf1, 0x2e, 0xc4, 0x4b, 0x36, 0x26, 0x92, 0xdf, 0x94, 0x13, 0x7f, 0x32, 
	0x8f, 0xea, 0x8d, 0xa7, 0x39, 0x90, 0x26, 0x5e, 0xc1, 0xbb, 0xbe, 0xa1, 0xae, 0x9a, 0xf0, 0xca, 
	0x13, 0xb2, 0x5a, 0xa2, 0x6c, 0xb4, 0xa6, 0x48, 0xcb, 0x9b, 0x9d, 0x1b, 0xe6, 0x5b, 0x2c, 0x09, 
	0x24, 0xa6, 0x6c, 0x54, 0xd5, 0x45, 0xec, 0x1b, 0x73, 0x74, 0xf4, 0x87, 0x2e, 0x99, 0xf0, 0x96]

property TV4_block_correct = ChaCha20_block_correct TV4_block_Key TV4_block_Nonce TV4_block_BlockCounter TV4_block_After20 TV4_block_KeyStream

```

### Test Vector #5

```cryptol
TV5_block_Key = (zero):ChaChaKey
TV5_block_Nonce = zero # 0x02:[96]
TV5_block_BlockCounter = 0

TV5_block_After20 = [
	0x374dc6c2, 0x3736d58c, 0xb904e24a, 0xcd3f93ef,
	0x88228b1a, 0x96a4dfb3, 0x5b76ab72, 0xc727ee54,
	0x0e0e978a, 0xf3145c95, 0x1b748ea8, 0xf786c297,
	0x99c28f5f, 0x628314e8, 0x398a19fa, 0x6ded1b53]
	
TV5_block_KeyStream = [
	0xc2, 0xc6, 0x4d, 0x37, 0x8c, 0xd5, 0x36, 0x37, 0x4a, 0xe2, 0x04, 0xb9, 0xef, 0x93, 0x3f, 0xcd,
	0x1a, 0x8b, 0x22, 0x88, 0xb3, 0xdf, 0xa4, 0x96, 0x72, 0xab, 0x76, 0x5b, 0x54, 0xee, 0x27, 0xc7,
	0x8a, 0x97, 0x0e, 0x0e, 0x95, 0x5c, 0x14, 0xf3, 0xa8, 0x8e, 0x74, 0x1b, 0x97, 0xc2, 0x86, 0xf7,
	0x5f, 0x8f, 0xc2, 0x99, 0xe8, 0x14, 0x83, 0x62, 0xfa, 0x19, 0x8a, 0x39, 0x53, 0x1b, 0xed, 0x6d]

property TV5_block_correct = ChaCha20_block_correct TV5_block_Key TV5_block_Nonce TV5_block_BlockCounter TV5_block_After20 TV5_block_KeyStream

property all_block_tests_correct =
	TV1_block_correct &&
	TV2_block_correct &&
	TV3_block_correct &&
	TV4_block_correct &&
	TV5_block_correct 
	
```

## ChaCha20 Encryption

```cryptol
ChaCha20_enc_correct key nonce blockcounter plaintext cyphertext = ChaCha20EncryptBytes plaintext key nonce blockcounter == cyphertext
```

### Test Vector #1

```cryptol
TV1_enc_Key = (zero):ChaChaKey
TV1_enc_Nonce = zero:[96]
TV1_enc_BlockCounter = 0

TV1_enc_plaintext = zero:[64][8]

TV1_enc_cyphertext = [
	0x76, 0xb8, 0xe0, 0xad, 0xa0, 0xf1, 0x3d, 0x90, 0x40, 0x5d, 0x6a, 0xe5, 0x53, 0x86, 0xbd, 0x28,
	0xbd, 0xd2, 0x19, 0xb8, 0xa0, 0x8d, 0xed, 0x1a, 0xa8, 0x36, 0xef, 0xcc, 0x8b, 0x77, 0x0d, 0xc7,
	0xda, 0x41, 0x59, 0x7c, 0x51, 0x57, 0x48, 0x8d, 0x77, 0x24, 0xe0, 0x3f, 0xb8, 0xd8, 0x4a, 0x37,
	0x6a, 0x43, 0xb8, 0xf4, 0x15, 0x18, 0xa1, 0x1c, 0xc3, 0x87, 0xb6, 0x69, 0xb2, 0xee, 0x65, 0x86]
	
property TV1_enc_correct = ChaCha20_enc_correct TV1_enc_Key TV1_enc_Nonce TV1_enc_BlockCounter TV1_enc_plaintext TV1_enc_cyphertext

```

### Test Vector #2

```cryptol
TV2_enc_Key = (zero # 0x1):ChaChaKey
TV2_enc_Nonce = zero # 0x2:[96]
TV2_enc_BlockCounter = 1

IETF_submission_text = [
	0x41, 0x6e, 0x79, 0x20, 0x73, 0x75, 0x62, 0x6d, 0x69, 0x73, 0x73, 0x69, 0x6f, 0x6e, 0x20, 0x74,
	0x6f, 0x20, 0x74, 0x68, 0x65, 0x20, 0x49, 0x45, 0x54, 0x46, 0x20, 0x69, 0x6e, 0x74, 0x65, 0x6e,
	0x64, 0x65, 0x64, 0x20, 0x62, 0x79, 0x20, 0x74, 0x68, 0x65, 0x20, 0x43, 0x6f, 0x6e, 0x74, 0x72,
	0x69, 0x62, 0x75, 0x74, 0x6f, 0x72, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x70, 0x75, 0x62, 0x6c, 0x69,
	0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x20, 0x61, 0x73, 0x20, 0x61, 0x6c, 0x6c, 0x20, 0x6f, 0x72,
	0x20, 0x70, 0x61, 0x72, 0x74, 0x20, 0x6f, 0x66, 0x20, 0x61, 0x6e, 0x20, 0x49, 0x45, 0x54, 0x46,
	0x20, 0x49, 0x6e, 0x74, 0x65, 0x72, 0x6e, 0x65, 0x74, 0x2d, 0x44, 0x72, 0x61, 0x66, 0x74, 0x20,
	0x6f, 0x72, 0x20, 0x52, 0x46, 0x43, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x61, 0x6e, 0x79, 0x20, 0x73,
	0x74, 0x61, 0x74, 0x65, 0x6d, 0x65, 0x6e, 0x74, 0x20, 0x6d, 0x61, 0x64, 0x65, 0x20, 0x77, 0x69,
	0x74, 0x68, 0x69, 0x6e, 0x20, 0x74, 0x68, 0x65, 0x20, 0x63, 0x6f, 0x6e, 0x74, 0x65, 0x78, 0x74,
	0x20, 0x6f, 0x66, 0x20, 0x61, 0x6e, 0x20, 0x49, 0x45, 0x54, 0x46, 0x20, 0x61, 0x63, 0x74, 0x69,
	0x76, 0x69, 0x74, 0x79, 0x20, 0x69, 0x73, 0x20, 0x63, 0x6f, 0x6e, 0x73, 0x69, 0x64, 0x65, 0x72,
	0x65, 0x64, 0x20, 0x61, 0x6e, 0x20, 0x22, 0x49, 0x45, 0x54, 0x46, 0x20, 0x43, 0x6f, 0x6e, 0x74,
	0x72, 0x69, 0x62, 0x75, 0x74, 0x69, 0x6f, 0x6e, 0x22, 0x2e, 0x20, 0x53, 0x75, 0x63, 0x68, 0x20,
	0x73, 0x74, 0x61, 0x74, 0x65, 0x6d, 0x65, 0x6e, 0x74, 0x73, 0x20, 0x69, 0x6e, 0x63, 0x6c, 0x75,
	0x64, 0x65, 0x20, 0x6f, 0x72, 0x61, 0x6c, 0x20, 0x73, 0x74, 0x61, 0x74, 0x65, 0x6d, 0x65, 0x6e,
	0x74, 0x73, 0x20, 0x69, 0x6e, 0x20, 0x49, 0x45, 0x54, 0x46, 0x20, 0x73, 0x65, 0x73, 0x73, 0x69,
	0x6f, 0x6e, 0x73, 0x2c, 0x20, 0x61, 0x73, 0x20, 0x77, 0x65, 0x6c, 0x6c, 0x20, 0x61, 0x73, 0x20,
	0x77, 0x72, 0x69, 0x74, 0x74, 0x65, 0x6e, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x65, 0x6c, 0x65, 0x63,
	0x74, 0x72, 0x6f, 0x6e, 0x69, 0x63, 0x20, 0x63, 0x6f, 0x6d, 0x6d, 0x75, 0x6e, 0x69, 0x63, 0x61,
	0x74, 0x69, 0x6f, 0x6e, 0x73, 0x20, 0x6d, 0x61, 0x64, 0x65, 0x20, 0x61, 0x74, 0x20, 0x61, 0x6e,
	0x79, 0x20, 0x74, 0x69, 0x6d, 0x65, 0x20, 0x6f, 0x72, 0x20, 0x70, 0x6c, 0x61, 0x63, 0x65, 0x2c,
	0x20, 0x77, 0x68, 0x69, 0x63, 0x68, 0x20, 0x61, 0x72, 0x65, 0x20, 0x61, 0x64, 0x64, 0x72, 0x65,
	0x73, 0x73, 0x65, 0x64, 0x20, 0x74, 0x6f ]
	
TV2_enc_plaintext = IETF_submission_text


TV2_enc_cyphertext = [
	0xa3, 0xfb, 0xf0, 0x7d, 0xf3, 0xfa, 0x2f, 0xde, 0x4f, 0x37, 0x6c, 0xa2, 0x3e, 0x82, 0x73, 0x70,
	0x41, 0x60, 0x5d, 0x9f, 0x4f, 0x4f, 0x57, 0xbd, 0x8c, 0xff, 0x2c, 0x1d, 0x4b, 0x79, 0x55, 0xec,
	0x2a, 0x97, 0x94, 0x8b, 0xd3, 0x72, 0x29, 0x15, 0xc8, 0xf3, 0xd3, 0x37, 0xf7, 0xd3, 0x70, 0x05,
	0x0e, 0x9e, 0x96, 0xd6, 0x47, 0xb7, 0xc3, 0x9f, 0x56, 0xe0, 0x31, 0xca, 0x5e, 0xb6, 0x25, 0x0d,
	0x40, 0x42, 0xe0, 0x27, 0x85, 0xec, 0xec, 0xfa, 0x4b, 0x4b, 0xb5, 0xe8, 0xea, 0xd0, 0x44, 0x0e,
	0x20, 0xb6, 0xe8, 0xdb, 0x09, 0xd8, 0x81, 0xa7, 0xc6, 0x13, 0x2f, 0x42, 0x0e, 0x52, 0x79, 0x50,
	0x42, 0xbd, 0xfa, 0x77, 0x73, 0xd8, 0xa9, 0x05, 0x14, 0x47, 0xb3, 0x29, 0x1c, 0xe1, 0x41, 0x1c,
	0x68, 0x04, 0x65, 0x55, 0x2a, 0xa6, 0xc4, 0x05, 0xb7, 0x76, 0x4d, 0x5e, 0x87, 0xbe, 0xa8, 0x5a,
	0xd0, 0x0f, 0x84, 0x49, 0xed, 0x8f, 0x72, 0xd0, 0xd6, 0x62, 0xab, 0x05, 0x26, 0x91, 0xca, 0x66,
	0x42, 0x4b, 0xc8, 0x6d, 0x2d, 0xf8, 0x0e, 0xa4, 0x1f, 0x43, 0xab, 0xf9, 0x37, 0xd3, 0x25, 0x9d,
	0xc4, 0xb2, 0xd0, 0xdf, 0xb4, 0x8a, 0x6c, 0x91, 0x39, 0xdd, 0xd7, 0xf7, 0x69, 0x66, 0xe9, 0x28,
	0xe6, 0x35, 0x55, 0x3b, 0xa7, 0x6c, 0x5c, 0x87, 0x9d, 0x7b, 0x35, 0xd4, 0x9e, 0xb2, 0xe6, 0x2b,
	0x08, 0x71, 0xcd, 0xac, 0x63, 0x89, 0x39, 0xe2, 0x5e, 0x8a, 0x1e, 0x0e, 0xf9, 0xd5, 0x28, 0x0f,
	0xa8, 0xca, 0x32, 0x8b, 0x35, 0x1c, 0x3c, 0x76, 0x59, 0x89, 0xcb, 0xcf, 0x3d, 0xaa, 0x8b, 0x6c,
	0xcc, 0x3a, 0xaf, 0x9f, 0x39, 0x79, 0xc9, 0x2b, 0x37, 0x20, 0xfc, 0x88, 0xdc, 0x95, 0xed, 0x84,
	0xa1, 0xbe, 0x05, 0x9c, 0x64, 0x99, 0xb9, 0xfd, 0xa2, 0x36, 0xe7, 0xe8, 0x18, 0xb0, 0x4b, 0x0b,
	0xc3, 0x9c, 0x1e, 0x87, 0x6b, 0x19, 0x3b, 0xfe, 0x55, 0x69, 0x75, 0x3f, 0x88, 0x12, 0x8c, 0xc0,
	0x8a, 0xaa, 0x9b, 0x63, 0xd1, 0xa1, 0x6f, 0x80, 0xef, 0x25, 0x54, 0xd7, 0x18, 0x9c, 0x41, 0x1f,
	0x58, 0x69, 0xca, 0x52, 0xc5, 0xb8, 0x3f, 0xa3, 0x6f, 0xf2, 0x16, 0xb9, 0xc1, 0xd3, 0x00, 0x62,
	0xbe, 0xbc, 0xfd, 0x2d, 0xc5, 0xbc, 0xe0, 0x91, 0x19, 0x34, 0xfd, 0xa7, 0x9a, 0x86, 0xf6, 0xe6,
	0x98, 0xce, 0xd7, 0x59, 0xc3, 0xff, 0x9b, 0x64, 0x77, 0x33, 0x8f, 0x3d, 0xa4, 0xf9, 0xcd, 0x85,
	0x14, 0xea, 0x99, 0x82, 0xcc, 0xaf, 0xb3, 0x41, 0xb2, 0x38, 0x4d, 0xd9, 0x02, 0xf3, 0xd1, 0xab,
	0x7a, 0xc6, 0x1d, 0xd2, 0x9c, 0x6f, 0x21, 0xba, 0x5b, 0x86, 0x2f, 0x37, 0x30, 0xe3, 0x7c, 0xfd,
	0xc4, 0xfd, 0x80, 0x6c, 0x22, 0xf2, 0x21]
	
property TV2_enc_correct = ChaCha20_enc_correct TV2_enc_Key TV2_enc_Nonce TV2_enc_BlockCounter TV2_enc_plaintext TV2_enc_cyphertext

```

### Test Vector #3

```cryptol
TV3_enc_Key = join([
	0x1c, 0x92, 0x40, 0xa5, 0xeb, 0x55, 0xd3, 0x8a, 0xf3, 0x33, 0x88, 0x86, 0x04, 0xf6, 0xb5, 0xf0,
	0x47, 0x39, 0x17, 0xc1, 0x40, 0x2b, 0x80, 0x09, 0x9d, 0xca, 0x5c, 0xbc, 0x20, 0x70, 0x75, 0xc0]):ChaChaKey
TV3_enc_Nonce = zero # 0x2:[96]
TV3_enc_BlockCounter = 42:[32]

jabberwock_text = [
	0x27, 0x54, 0x77, 0x61, 0x73, 0x20, 0x62, 0x72, 0x69, 0x6c, 0x6c, 0x69, 0x67, 0x2c, 0x20, 0x61,
	0x6e, 0x64, 0x20, 0x74, 0x68, 0x65, 0x20, 0x73, 0x6c, 0x69, 0x74, 0x68, 0x79, 0x20, 0x74, 0x6f,
	0x76, 0x65, 0x73, 0x0a, 0x44, 0x69, 0x64, 0x20, 0x67, 0x79, 0x72, 0x65, 0x20, 0x61, 0x6e, 0x64,
	0x20, 0x67, 0x69, 0x6d, 0x62, 0x6c, 0x65, 0x20, 0x69, 0x6e, 0x20, 0x74, 0x68, 0x65, 0x20, 0x77,
	0x61, 0x62, 0x65, 0x3a, 0x0a, 0x41, 0x6c, 0x6c, 0x20, 0x6d, 0x69, 0x6d, 0x73, 0x79, 0x20, 0x77,
	0x65, 0x72, 0x65, 0x20, 0x74, 0x68, 0x65, 0x20, 0x62, 0x6f, 0x72, 0x6f, 0x67, 0x6f, 0x76, 0x65,
	0x73, 0x2c, 0x0a, 0x41, 0x6e, 0x64, 0x20, 0x74, 0x68, 0x65, 0x20, 0x6d, 0x6f, 0x6d, 0x65, 0x20,
	0x72, 0x61, 0x74, 0x68, 0x73, 0x20, 0x6f, 0x75, 0x74, 0x67, 0x72, 0x61, 0x62, 0x65, 0x2e]
	
TV3_enc_plaintext = jabberwock_text


TV3_enc_cyphertext = [
	0x62, 0xe6, 0x34, 0x7f, 0x95, 0xed, 0x87, 0xa4, 0x5f, 0xfa, 0xe7, 0x42, 0x6f, 0x27, 0xa1, 0xdf,
	0x5f, 0xb6, 0x91, 0x10, 0x04, 0x4c, 0x0d, 0x73, 0x11, 0x8e, 0xff, 0xa9, 0x5b, 0x01, 0xe5, 0xcf,
	0x16, 0x6d, 0x3d, 0xf2, 0xd7, 0x21, 0xca, 0xf9, 0xb2, 0x1e, 0x5f, 0xb1, 0x4c, 0x61, 0x68, 0x71,
	0xfd, 0x84, 0xc5, 0x4f, 0x9d, 0x65, 0xb2, 0x83, 0x19, 0x6c, 0x7f, 0xe4, 0xf6, 0x05, 0x53, 0xeb,
	0xf3, 0x9c, 0x64, 0x02, 0xc4, 0x22, 0x34, 0xe3, 0x2a, 0x35, 0x6b, 0x3e, 0x76, 0x43, 0x12, 0xa6,
	0x1a, 0x55, 0x32, 0x05, 0x57, 0x16, 0xea, 0xd6, 0x96, 0x25, 0x68, 0xf8, 0x7d, 0x3f, 0x3f, 0x77,
	0x04, 0xc6, 0xa8, 0xd1, 0xbc, 0xd1, 0xbf, 0x4d, 0x50, 0xd6, 0x15, 0x4b, 0x6d, 0xa7, 0x31, 0xb1,
	0x87, 0xb5, 0x8d, 0xfd, 0x72, 0x8a, 0xfa, 0x36, 0x75, 0x7a, 0x79, 0x7a, 0xc1, 0x88, 0xd1]
	
property TV3_enc_correct = ChaCha20_enc_correct TV3_enc_Key TV3_enc_Nonce TV3_enc_BlockCounter TV3_enc_plaintext TV3_enc_cyphertext

property all_enc_tests_correct =
	TV1_enc_correct &&
	TV2_enc_correct &&
	TV3_enc_correct 
```

## Poly1305 Message Authentication Code

```cryptol
poly1305_MAC_correct key text tag = Poly1305 key text == tag
```

### Test Vector #1

```cryptol
TV1_MAC_Key = zero:[256]

TV1_MAC_text = zero:[64][8]

TV1_MAC_tag = zero : [16][8]

property TV1_MAC_correct = poly1305_MAC_correct TV1_MAC_Key TV1_MAC_text TV1_MAC_tag
```

### Test Vector #2

```cryptol
reused_key = [0x36, 0xe5, 0xf6, 0xb5, 0xc5, 0xe0, 0x60, 0x70, 0xf0, 0xef, 0xca, 0x96, 0x22, 0x7a, 0x86, 0x3e]
TV2_MAC_Key = zero # join(reused_key):[256]

TV2_MAC_text = IETF_submission_text

TV2_MAC_tag = reused_key: [16][8]

property TV2_MAC_correct = poly1305_MAC_correct TV2_MAC_Key TV2_MAC_text TV2_MAC_tag
```

### Test Vector #3

```cryptol
TV3_MAC_Key = join(reused_key) # 0:[256]

TV3_MAC_text = IETF_submission_text

TV3_MAC_tag = [0xf3, 0x47, 0x7e, 0x7c, 0xd9, 0x54, 0x17, 0xaf, 0x89, 0xa6, 0xb8, 0x79, 0x4c, 0x31, 0x0c, 0xf0]: [16][8]

property TV3_MAC_correct = poly1305_MAC_correct TV3_MAC_Key TV3_MAC_text TV3_MAC_tag
```

### Test Vector #4

```cryptol
TV4_MAC_Key =  join(
	[0x1c, 0x92, 0x40, 0xa5, 0xeb, 0x55, 0xd3, 0x8a, 0xf3, 0x33, 0x88, 0x86, 0x04, 0xf6, 0xb5, 0xf0,
	 0x47, 0x39, 0x17, 0xc1, 0x40, 0x2b, 0x80, 0x09, 0x9d, 0xca, 0x5c, 0xbc, 0x20, 0x70, 0x75, 0xc0]):[256]

TV4_MAC_text = jabberwock_text

TV4_MAC_tag = [0x45, 0x41, 0x66, 0x9a, 0x7e, 0xaa, 0xee, 0x61, 0xe7, 0x08, 0xdc, 0x7c, 0xbc, 0xc5, 0xeb, 0x62]: [16][8]

property TV4_MAC_correct = poly1305_MAC_correct TV4_MAC_Key TV4_MAC_text TV4_MAC_tag
```

### Test Vector #5

If one uses 130-bit partial reduction, does the code
handle the case where partially reduced final result is not fully
reduced?

```cryptol

TV5_MAC_Key =  0x02 # zero:[256]

FF_16 = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
TV5_MAC_text = FF_16

TV5_MAC_tag = split(0x03 # zero): [16][8]

property TV5_MAC_correct = poly1305_MAC_correct TV5_MAC_Key TV5_MAC_text TV5_MAC_tag
```

### Test Vector #6

What happens if addition of s overflows modulo 2^128?

```cryptol
TV6_MAC_Key =  0x02 # zero # join(FF_16):[256]

TV6_MAC_text = split(0x02 # zero) : [16][8]

TV6_MAC_tag = split(0x03 # 0): [16][8]

property TV6_MAC_correct = poly1305_MAC_correct TV6_MAC_Key TV6_MAC_text TV6_MAC_tag
```

### Test Vector #7

What happens if data limb is all ones and there is
carry from lower limb?

```cryptol

TV7_MAC_Key =  0x01 # zero:[256]

TV7_MAC_text = [
	0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

TV7_MAC_tag = split(0x05 # zero): [16][8]

property TV7_MAC_correct = poly1305_MAC_correct TV7_MAC_Key TV7_MAC_text TV7_MAC_tag
```

### Test Vector #8

What happens if final result from polynomial part is
exactly 2^130-5?

```cryptol

TV8_MAC_Key =  0x01 # zero:[256]

TV8_MAC_text = [
	0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
	0xFB, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE, 0xFE,
	0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01]

TV8_MAC_tag = split(zero): [16][8]

property TV8_MAC_correct = poly1305_MAC_correct TV8_MAC_Key TV8_MAC_text TV8_MAC_tag
```

### Test Vector #9

What happens if final result from polynomial part is
exactly 2^130-6?

```cryptol

TV9_MAC_Key =  0x02 # zero:[256]

TV9_MAC_text = 
	[0xFD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]

TV9_MAC_tag = [0xFA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]: [16][8]

property TV9_MAC_correct = poly1305_MAC_correct TV9_MAC_Key TV9_MAC_text TV9_MAC_tag
```

### Test Vector #10

What happens if 5*H+L-type reduction produces 131-
bit intermediate result?

```cryptol

TV10_MAC_Key =  join([0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) # 0 :[256]

TV10_MAC_text = [
	0xE3, 0x35, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x33, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0x79, 0xCD, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

TV10_MAC_tag = [0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]: [16][8]

property TV10_MAC_correct = poly1305_MAC_correct TV10_MAC_Key TV10_MAC_text TV10_MAC_tag
```

### Test Vector #11

What happens if 5*H+L-type reduction produces 131-
bit final result?

```cryptol

TV11_MAC_Key =  join([0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]) # 0 :[256]

TV11_MAC_text = [
	0xE3, 0x35, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x33, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0x79, 0xCD, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
	
TV11_MAC_tag = split(0x13 # 0): [16][8]

property TV11_MAC_correct = poly1305_MAC_correct TV11_MAC_Key TV11_MAC_text TV11_MAC_tag

property all_MAC_tests_correct =
	TV1_MAC_correct &&
	TV2_MAC_correct &&
	TV3_MAC_correct &&
	TV4_MAC_correct &&
	TV5_MAC_correct &&
	TV6_MAC_correct &&
	TV7_MAC_correct &&
	TV8_MAC_correct &&
	TV9_MAC_correct &&
	TV10_MAC_correct &&
	TV11_MAC_correct 

```

## Poly1305 Key Generation Using ChaCha20

```cryptol
Poly1305_key_correct key nonce otk = GeneratePolyKeyUsingChaCha key nonce 0 == otk
```

### Test Vector #1

```cryptol
TV1_key_Key = zero:ChaChaKey
TV1_key_Nonce = zero:[96]

TV1_key_OneTimeKey = join([
	0x76, 0xb8, 0xe0, 0xad, 0xa0, 0xf1, 0x3d, 0x90, 0x40, 0x5d, 0x6a, 0xe5, 0x53, 0x86, 0xbd, 0x28,
	0xbd, 0xd2, 0x19, 0xb8, 0xa0, 0x8d, 0xed, 0x1a, 0xa8, 0x36, 0xef, 0xcc, 0x8b, 0x77, 0x0d, 0xc7])

property TV1_key_correct = Poly1305_key_correct TV1_key_Key TV1_key_Nonce TV1_key_OneTimeKey
```

### Test Vector #2

```cryptol
TV2_key_Key = zero # 0x01:ChaChaKey
TV2_key_Nonce = zero # 0x02:[96]

TV2_key_OneTimeKey = join([
	0xec, 0xfa, 0x25, 0x4f, 0x84, 0x5f, 0x64, 0x74, 0x73, 0xd3, 0xcb, 0x14, 0x0d, 0xa9, 0xe8, 0x76,
	0x06, 0xcb, 0x33, 0x06, 0x6c, 0x44, 0x7b, 0x87, 0xbc, 0x26, 0x66, 0xdd, 0xe3, 0xfb, 0xb7, 0x39])

property TV2_key_correct = Poly1305_key_correct TV2_key_Key TV2_key_Nonce TV2_key_OneTimeKey
```

### Test Vector #3

```cryptol
TV3_key_Key = join([
	0x1c, 0x92, 0x40, 0xa5, 0xeb, 0x55, 0xd3, 0x8a, 0xf3, 0x33, 0x88, 0x86, 0x04, 0xf6, 0xb5, 0xf0,
	0x47, 0x39, 0x17, 0xc1, 0x40, 0x2b, 0x80, 0x09, 0x9d, 0xca, 0x5c, 0xbc, 0x20, 0x70, 0x75, 0xc0]):ChaChaKey
TV3_key_Nonce = zero # 0x02:[96]

TV3_key_OneTimeKey = join([
	0x96, 0x5e, 0x3b, 0xc6, 0xf9, 0xec, 0x7e, 0xd9, 0x56, 0x08, 0x08, 0xf4, 0xd2, 0x29, 0xf9, 0x4b,
	0x13, 0x7f, 0xf2, 0x75, 0xca, 0x9b, 0x3f, 0xcb, 0xdd, 0x59, 0xde, 0xaa, 0xd2, 0x33, 0x10, 0xae])

property TV3_key_correct = Poly1305_key_correct TV3_key_Key TV3_key_Nonce TV3_key_OneTimeKey

property all_key_tests_correct =
	TV1_key_correct &&
	TV2_key_correct &&
	TV3_key_correct 
```

## ChaCha20-Poly1305 AEAD Decryption

Below we’ll see decrypting a message. We receive a ciphertext, a
nonce, and a tag. We know the key. We will check the tag, and then
(assuming that it validates) decrypt the ciphertext. In this
particular protocol, we’ll assume that there is no padding of the
plaintext.

```cryptol
AEAD_correct key nonce cypherText tag AAD = ptMatches && isValid where
    (pt,isValid) = AEAD_CHACHA20_POLY1305_DECRYPT key nonce cypherText AAD
    cypherText   = (AEAD_CHACHA20_POLY1305 key nonce AeadPt AAD)
    ptMatches    = tag == pt
```

```cryptol
//known
TV1_AEAD_key = join([
	0x1c, 0x92, 0x40, 0xa5, 0xeb, 0x55, 0xd3, 0x8a, 0xf3, 0x33, 0x88, 0x86, 0x04, 0xf6, 0xb5, 0xf0,
	0x47, 0x39, 0x17, 0xc1, 0x40, 0x2b, 0x80, 0x09, 0x9d, 0xca, 0x5c, 0xbc, 0x20, 0x70, 0x75, 0xc0])

//sent
TV1_AEAD_nonce = join([0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08])

//sent
TV1_AEAD_AAD = [0xf3, 0x33, 0x88, 0x86, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4e, 0x91]

//	calculated
TV1_AEAD_known_otk = join([
	0xbd, 0xf0, 0x4a, 0xa9, 0x5c, 0xe4, 0xde, 0x89, 0x95, 0xb1, 0x4b, 0xb6, 0xa1, 0x8f, 0xec, 0xaf,
	0x26, 0x47, 0x8f, 0x50, 0xc0, 0x54, 0xf5, 0x63, 0xdb, 0xc0, 0xa2, 0x1e, 0x26, 0x15, 0x72, 0xaa])

//sent
TV1_AEAD_tag = [0xee, 0xad, 0x9d, 0x67, 0x89, 0x0c, 0xbb, 0x22, 0x39, 0x23, 0x36, 0xfe, 0xa1, 0x85, 0x1f, 0x38]
	
TV1_AEAD_cypherText = [
	0x64, 0xa0, 0x86, 0x15, 0x75, 0x86, 0x1a, 0xf4, 0x60, 0xf0, 0x62, 0xc7, 0x9b, 0xe6, 0x43, 0xbd,
	0x5e, 0x80, 0x5c, 0xfd, 0x34, 0x5c, 0xf3, 0x89, 0xf1, 0x08, 0x67, 0x0a, 0xc7, 0x6c, 0x8c, 0xb2,
	0x4c, 0x6c, 0xfc, 0x18, 0x75, 0x5d, 0x43, 0xee, 0xa0, 0x9e, 0xe9, 0x4e, 0x38, 0x2d, 0x26, 0xb0,
	0xbd, 0xb7, 0xb7, 0x3c, 0x32, 0x1b, 0x01, 0x00, 0xd4, 0xf0, 0x3b, 0x7f, 0x35, 0x58, 0x94, 0xcf,
	0x33, 0x2f, 0x83, 0x0e, 0x71, 0x0b, 0x97, 0xce, 0x98, 0xc8, 0xa8, 0x4a, 0xbd, 0x0b, 0x94, 0x81,
	0x14, 0xad, 0x17, 0x6e, 0x00, 0x8d, 0x33, 0xbd, 0x60, 0xf9, 0x82, 0xb1, 0xff, 0x37, 0xc8, 0x55,
	0x97, 0x97, 0xa0, 0x6e, 0xf4, 0xf0, 0xef, 0x61, 0xc1, 0x86, 0x32, 0x4e, 0x2b, 0x35, 0x06, 0x38,
	0x36, 0x06, 0x90, 0x7b, 0x6a, 0x7c, 0x02, 0xb0, 0xf9, 0xf6, 0x15, 0x7b, 0x53, 0xc8, 0x67, 0xe4,
	0xb9, 0x16, 0x6c, 0x76, 0x7b, 0x80, 0x4d, 0x46, 0xa5, 0x9b, 0x52, 0x16, 0xcd, 0xe7, 0xa4, 0xe9,
	0x90, 0x40, 0xc5, 0xa4, 0x04, 0x33, 0x22, 0x5e, 0xe2, 0x82, 0xa1, 0xb0, 0xa0, 0x6c, 0x52, 0x3e,
	0xaf, 0x45, 0x34, 0xd7, 0xf8, 0x3f, 0xa1, 0x15, 0x5b, 0x00, 0x47, 0x71, 0x8c, 0xbc, 0x54, 0x6a,
	0x0d, 0x07, 0x2b, 0x04, 0xb3, 0x56, 0x4e, 0xea, 0x1b, 0x42, 0x22, 0x73, 0xf5, 0x48, 0x27, 0x1a,
	0x0b, 0xb2, 0x31, 0x60, 0x53, 0xfa, 0x76, 0x99, 0x19, 0x55, 0xeb, 0xd6, 0x31, 0x59, 0x43, 0x4e,
	0xce, 0xbb, 0x4e, 0x46, 0x6d, 0xae, 0x5a, 0x10, 0x73, 0xa6, 0x72, 0x76, 0x27, 0x09, 0x7a, 0x10,
	0x49, 0xe6, 0x17, 0xd9, 0x1d, 0x36, 0x10, 0x94, 0xfa, 0x68, 0xf0, 0xff, 0x77, 0x98, 0x71, 0x30,
	0x30, 0x5b, 0xea, 0xba, 0x2e, 0xda, 0x04, 0xdf, 0x99, 0x7b, 0x71, 0x4d, 0x6c, 0x6f, 0x2c, 0x29,
	0xa6, 0xad, 0x5c, 0xb4, 0x02, 0x2b, 0x02, 0x70, 0x9b]

TV1_AEAD_Poly_input = [
	0xf3, 0x33, 0x88, 0x86, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4e, 0x91, 0x00, 0x00, 0x00, 0x00,
	0x64, 0xa0, 0x86, 0x15, 0x75, 0x86, 0x1a, 0xf4, 0x60, 0xf0, 0x62, 0xc7, 0x9b, 0xe6, 0x43, 0xbd,
	0x5e, 0x80, 0x5c, 0xfd, 0x34, 0x5c, 0xf3, 0x89, 0xf1, 0x08, 0x67, 0x0a, 0xc7, 0x6c, 0x8c, 0xb2,
	0x4c, 0x6c, 0xfc, 0x18, 0x75, 0x5d, 0x43, 0xee, 0xa0, 0x9e, 0xe9, 0x4e, 0x38, 0x2d, 0x26, 0xb0,
	0xbd, 0xb7, 0xb7, 0x3c, 0x32, 0x1b, 0x01, 0x00, 0xd4, 0xf0, 0x3b, 0x7f, 0x35, 0x58, 0x94, 0xcf,
	0x33, 0x2f, 0x83, 0x0e, 0x71, 0x0b, 0x97, 0xce, 0x98, 0xc8, 0xa8, 0x4a, 0xbd, 0x0b, 0x94, 0x81,
	0x14, 0xad, 0x17, 0x6e, 0x00, 0x8d, 0x33, 0xbd, 0x60, 0xf9, 0x82, 0xb1, 0xff, 0x37, 0xc8, 0x55,
	0x97, 0x97, 0xa0, 0x6e, 0xf4, 0xf0, 0xef, 0x61, 0xc1, 0x86, 0x32, 0x4e, 0x2b, 0x35, 0x06, 0x38,
	0x36, 0x06, 0x90, 0x7b, 0x6a, 0x7c, 0x02, 0xb0, 0xf9, 0xf6, 0x15, 0x7b, 0x53, 0xc8, 0x67, 0xe4,
	0xb9, 0x16, 0x6c, 0x76, 0x7b, 0x80, 0x4d, 0x46, 0xa5, 0x9b, 0x52, 0x16, 0xcd, 0xe7, 0xa4, 0xe9,
	0x90, 0x40, 0xc5, 0xa4, 0x04, 0x33, 0x22, 0x5e, 0xe2, 0x82, 0xa1, 0xb0, 0xa0, 0x6c, 0x52, 0x3e,
	0xaf, 0x45, 0x34, 0xd7, 0xf8, 0x3f, 0xa1, 0x15, 0x5b, 0x00, 0x47, 0x71, 0x8c, 0xbc, 0x54, 0x6a,
	0x0d, 0x07, 0x2b, 0x04, 0xb3, 0x56, 0x4e, 0xea, 0x1b, 0x42, 0x22, 0x73, 0xf5, 0x48, 0x27, 0x1a,
	0x0b, 0xb2, 0x31, 0x60, 0x53, 0xfa, 0x76, 0x99, 0x19, 0x55, 0xeb, 0xd6, 0x31, 0x59, 0x43, 0x4e,
	0xce, 0xbb, 0x4e, 0x46, 0x6d, 0xae, 0x5a, 0x10, 0x73, 0xa6, 0x72, 0x76, 0x27, 0x09, 0x7a, 0x10,
	0x49, 0xe6, 0x17, 0xd9, 0x1d, 0x36, 0x10, 0x94, 0xfa, 0x68, 0xf0, 0xff, 0x77, 0x98, 0x71, 0x30,
	0x30, 0x5b, 0xea, 0xba, 0x2e, 0xda, 0x04, 0xdf, 0x99, 0x7b, 0x71, 0x4d, 0x6c, 0x6f, 0x2c, 0x29,
	0xa6, 0xad, 0x5c, 0xb4, 0x02, 0x2b, 0x02, 0x70, 0x9b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x09, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
```

First, we calculate the one-time Poly1305 key

```cryptol
	
//generate and check the one time key (leaving out the given states from the document, they will be correct if this is correct)
property TV1_otk_correct = Poly1305_key_correct TV1_AEAD_key TV1_AEAD_nonce TV1_AEAD_known_otk

```

Next, we construct the AEAD buffer

```cryptol
// Helper macros for further properties
poly_input_correct AeadAAD cypherText result = (AeadConstruction AeadAAD cypherText) == result

property TV1_poly_input_correct = (poly_input_correct TV1_AEAD_AAD TV1_AEAD_cypherText TV1_AEAD_Poly_input)
```

We calculate the Poly1305 tag and find that it matches

```cryptol
property TV1_tag_correct = poly1305_MAC_correct TV1_AEAD_known_otk (AeadConstruction TV1_AEAD_AAD TV1_AEAD_cypherText) TV1_AEAD_tag
```
	
```cryptol
TV1_plaintext = [
	0x49, 0x6e, 0x74, 0x65, 0x72, 0x6e, 0x65, 0x74, 0x2d, 0x44, 0x72, 0x61, 0x66, 0x74, 0x73, 0x20,
	0x61, 0x72, 0x65, 0x20, 0x64, 0x72, 0x61, 0x66, 0x74, 0x20, 0x64, 0x6f, 0x63, 0x75, 0x6d, 0x65,
	0x6e, 0x74, 0x73, 0x20, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x61, 0x20,
	0x6d, 0x61, 0x78, 0x69, 0x6d, 0x75, 0x6d, 0x20, 0x6f, 0x66, 0x20, 0x73, 0x69, 0x78, 0x20, 0x6d,
	0x6f, 0x6e, 0x74, 0x68, 0x73, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x6d, 0x61, 0x79, 0x20, 0x62, 0x65,
	0x20, 0x75, 0x70, 0x64, 0x61, 0x74, 0x65, 0x64, 0x2c, 0x20, 0x72, 0x65, 0x70, 0x6c, 0x61, 0x63,
	0x65, 0x64, 0x2c, 0x20, 0x6f, 0x72, 0x20, 0x6f, 0x62, 0x73, 0x6f, 0x6c, 0x65, 0x74, 0x65, 0x64,
	0x20, 0x62, 0x79, 0x20, 0x6f, 0x74, 0x68, 0x65, 0x72, 0x20, 0x64, 0x6f, 0x63, 0x75, 0x6d, 0x65,
	0x6e, 0x74, 0x73, 0x20, 0x61, 0x74, 0x20, 0x61, 0x6e, 0x79, 0x20, 0x74, 0x69, 0x6d, 0x65, 0x2e,
	0x20, 0x49, 0x74, 0x20, 0x69, 0x73, 0x20, 0x69, 0x6e, 0x61, 0x70, 0x70, 0x72, 0x6f, 0x70, 0x72,
	0x69, 0x61, 0x74, 0x65, 0x20, 0x74, 0x6f, 0x20, 0x75, 0x73, 0x65, 0x20, 0x49, 0x6e, 0x74, 0x65,
	0x72, 0x6e, 0x65, 0x74, 0x2d, 0x44, 0x72, 0x61, 0x66, 0x74, 0x73, 0x20, 0x61, 0x73, 0x20, 0x72,
	0x65, 0x66, 0x65, 0x72, 0x65, 0x6e, 0x63, 0x65, 0x20, 0x6d, 0x61, 0x74, 0x65, 0x72, 0x69, 0x61,
	0x6c, 0x20, 0x6f, 0x72, 0x20, 0x74, 0x6f, 0x20, 0x63, 0x69, 0x74, 0x65, 0x20, 0x74, 0x68, 0x65,
	0x6d, 0x20, 0x6f, 0x74, 0x68, 0x65, 0x72, 0x20, 0x74, 0x68, 0x61, 0x6e, 0x20, 0x61, 0x73, 0x20,
	0x2f, 0xe2, 0x80, 0x9c, 0x77, 0x6f, 0x72, 0x6b, 0x20, 0x69, 0x6e, 0x20, 0x70, 0x72, 0x6f, 0x67,
	0x72, 0x65, 0x73, 0x73, 0x2e, 0x2f, 0xe2, 0x80, 0x9d]
		

TV1_calculate_plaintext = AEAD_CHACHA20_POLY1305_DECRYPT TV1_AEAD_key TV1_AEAD_nonce (TV1_AEAD_cypherText # TV1_AEAD_tag) TV1_AEAD_AAD
	
property TV1_plaintext_correct = isValid && pt == TV1_plaintext where
	(pt,isValid) = TV1_calculate_plaintext
	
property decryption_vector_correct = 
	TV1_plaintext_correct &&
	TV1_tag_correct &&
	TV1_otk_correct


property all_test_vectors_correct =
  all_block_tests_correct &&
  all_enc_tests_correct &&
  all_MAC_tests_correct &&
  all_key_tests_correct &&
  decryption_vector_correct
```


# Appendix: Utility functions

```cryptol
indexOf e (xs:[a+1]b) = ixs ! 0 where
    ixs = [ 0 ] #
                 [ if ix == e then j else old
                 | ix <- xs
                 | j <- [ 0 .. a ]
                 | old <- ixs
                 ]

ToLittleEndian : ChaChaState -> ChaChaState
ToLittleEndian s = [littleendian (split words) | words <- s]

// Takes a finite sequence of bytes, and turns them into a word via
// a little-endian interpretation
littleendian : {a}(fin a) => [a][8] -> [a*8]
littleendian b = join(reverse b)

// Converts a bytestring encoded like "fe:ed:fa:ce." into a sequence of bytes
// Note: the trailing punctuation is needed
parseHexString : {n} (fin n) => [3*n][8] -> [n][8]
parseHexString hexString = [ charsToByte (take`{2} cs) | cs <- groupBy`{3} hexString ] where
    charsToByte : [2][8] -> [8]
    charsToByte [ ub, lb ] = (charToByte ub) << 4 || (charToByte lb)
    charToByte c = if c >= '0' && c <= '9' then c-'0'
                   | c >= 'a' && c <= 'f' then 10+(c-'a')
                   else 0     // error case

property parseHexString_check =
    join (parseHexString
        ("00:01:02:03:04:05:06:07:08:09:0a:0b:0c:0d:0e:0f:10:11:12:13:" #
         "14:15:16:17:18:19:1a:1b:1c:1d:1e:1f.")) ==
    0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f

property AllPropertiesPass = 
    ChaChaQuarterround_passes_test &&
    ChaChaQuarterround_passes_column_test &&
    FirstRow_correct &&
    BuildState_correct &&
    ChaChaStateAfter20_correct &&
    ChaCha20_test1 &&
    SunscreenBuildState_correct &&
    SunscreenBuildState2_correct &&
    SunscreenBlock1_correct &&
    SunscreenBlock2_correct &&
    SunscreenKeystream_correct SunscreenKeystream &&
    ChaCha_encrypt_sunscreen_correct &&
    Sunscreen_decrypt_correct &&
    poly1306Sokay &&
    polyBlocksOK &&
    Poly1305_passes_test &&
    PolyBuildState_correct &&
    PolyChaCha_correct &&
    Poly_passes_test &&
    AeadPolyKeyBuildState_correct &&
    AeadPolyChaCha_correct &&
    poly1305Test_correct &&
    AeadTag_correct &&
    AeadConstruction_correct &&
    AeadDecrypt_correct &&
    parseHexString_check &&
    all_test_vectors_correct

```

Since this file is literate Cryptol, the properties above can be checked
by loading it into a Cryptol interpreter, and running the AllPropertiesPass
function, like this:

```example
$ cryptol ChaChaPolyCryptolIETF.md 
                        _        _
   ___ _ __ _   _ _ __ | |_ ___ | |
  / __| '__| | | | '_ \| __/ _ \| |
 | (__| |  | |_| | |_) | || (_) | |
  \___|_|   \__, | .__/ \__\___/|_|
            |___/|_| version 2.0.0 (62acc96)

Loading module Cryptol
Loading module ChaCha20
... a bunch of warnings about the use of ambiguous-width constants
ChaCha20> AllPropertiesPass 
True
```
This check verifies the implementation of `ChaCha`, `Poly1305` and the `AEAD`
construction all work with the provided test vectors.



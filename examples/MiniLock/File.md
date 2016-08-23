Copyright (c) 2013-2016 Galois, Inc.
Distributed under the terms of the BSD3 license (see LICENSE file)

Define the minilock file format, encoding only.

```cryptol
module File where

import CfrgCurves
import Blake2s
import Base64
import Poly1305
import Salsa20
import CryptoBox
import Keys
```


The file format is:

> miniLock magic bytes (8 bytes)
> Header length in bytes (4 bytes, little-endian)
> Header bytes (JSON, fields sometimes encrypted)
> Ciphertext bytes

Variable sized formats are potentially awkward for Cryptol because Cryptol
encodes the length of values in the type. For example, the header size varies
in the JS implementation. Fortunately this variablity is all due to either the
arbitrary choices of the encoder or things deterministicly dependent on the
input type (vs value).  For an example of the later case, the number of
recipients leads to a variable header size that is computable from the input
type. The former is a larger issue - for example a Base58 encoding of 0 could
be an arbitrary number of the letter 'A' ("A", "AA", etc).  For encoding this
is handled by emitting the maximum encoding (46 bytes for minilock
identifications), but this issue prevents us from implementing a decoder that
would interoperate with anything interesting.


The header format is:

> {
> version: Version of the miniLock protocol used for this file (Currently 1) (Number)
> ephemeral: Public key from ephemeral key pair used to encrypt decryptInfo object (Base64),
> decryptInfo: {
>     (One copy of the below object for every recipient)
>     Unique nonce for decrypting this object (Base64): {
>         senderID: Sender's miniLock ID (Base58),
>         recipientID: miniLock ID of this recipient (used for verfication) (Base58),
>         fileInfo: {
>             fileKey: Key for file decryption (Base64),
>             fileNonce: Nonce for file decryption (Base64),
>             fileHash: BLAKE2 hash (32 bytes) of the ciphertext bytes. (Base64)
>         } (fileInfo is encrypted to recipient's public key using long-term key pair) (Base64),
>     } (encrypted to recipient's public key using ephemeral key pair) (Base64)
> }

```cryptol
// Size of a given minilock container depends soley on the number of recipients and the plaintext
type MiniLockBytes nrRecip fileSize = 8 + 4 + 89 + (DecryptInfoSize + 1) * nrRecip + EncryptedBytes fileSize - 1

minilock : {nrRecip, fileNameBytes, msgBytes}
        ( fin nrRecip, fin fileNameBytes, fin msgBytes  // All the values are finite
        , nrRecip >= 1, 22 >= width nrRecip             // Between 1 and 4M recipients
        , 63 >= width msgBytes                          // Messages leq 2^63 bytes
        , fileNameBytes >= 1, 256 >= fileNameBytes      // Between 1 and 256 byte file name
        ) =>
        [nrRecip](MinilockID,[24][8])    // Recipients and nonces for the fileInfo field
        -> [fileNameBytes][8]            // File name
        -> [msgBytes][8]                 // Plaintext
        -> (Private25519, Public25519)   // Sender keys
        -> [32][8]                       // File key (random)
        -> [16][8]                       // File nonce (random)
        -> (Private25519, Public25519)   // Ephemeral keys (random)
        -> [MiniLockBytes nrRecip msgBytes][8]
minilock rs fileName0 msg senderKeys fileKey fileNonce ephemKeys = lockFile
 where
  filename               = take `{256} (fileName0 # (zero : [256][8]))
  ct                     = encryptData fileKey fileNonce filename msg
  fileInfo               = mkFileInfoBlob (fileKey, fileNonce, split (blake2s `{nn=32} ct))
  lockFile               = mkMiniLock rs senderKeys ephemKeys fileInfo ct

private
  magic : [8][8]
  magic = [0x6d, 0x69, 0x6e, 0x69, 0x4c, 0x6f, 0x63, 0x6b]

  encryptData : {msgBytes} (63 >= width msgBytes)
             => [32][8]-> [16][8] -> [256][8] -> [msgBytes][8] -> [EncryptedBytes msgBytes][8]
  encryptData k n f m = encryptChunks k n f cs cN
   where
    (cs,cN) = mkChunks m

  // encrypt chunks results in the ciphertext AND poly1305 tag for each chunk.
  encryptChunks : {chunks,rem}
                  (fin chunks, fin rem
                  , 32 >= width rem
                  , 64 >= width chunks)
               => [32][8] -> [16][8] -> [256][8] -> [chunks]Chunk -> [rem][8]
               -> [4 + 16 + 256 + chunks*((2^^20) + 4 + 16) + 4 + 16 + rem][8]
  encryptChunks key nonce c0 cs end = encChunk0 # join ctChunks # ctFinal
    where
    fullNonce0 = nonce # put64le zero
    encChunk0  = put32le 256      # crypto_secretbox c0 key fullNonce0 : [4 + 16 + 256][8]

    nonces     = [nonce # put64le i | i <- [1...]]
    ctChunks   = [put32le (2^^20) # crypto_secretbox cnk key n | n <- nonces | cnk <- cs]

    nFinal     =  nonce # put64le ((`chunks + 1) || 0x8000000000000000)
    ctFinal    =  put32le `rem     # crypto_secretbox end key nFinal
```

The minilock file format is a concatenation of the magic, header length field, header, and ciphertext.

```cryptol

  // Size of the 'decryptInfo' javascript record.
  type DecryptInfoSize = 549


  mkMiniLock : {nrRecip, ctBytes} (22 >= width nrRecip, nrRecip >= 1) =>
               [nrRecip](MinilockID,[24][8])
            -> (Private25519, Public25519)
            -> (Private25519, Public25519)
            -> FileInfoBlob
            -> [ctBytes][8]
            -> [8 + 4 + 89 + (DecryptInfoSize + 1) * nrRecip + ctBytes - 1][8]
  mkMiniLock rs senderKeys ephemKeys fileInfo ct =
      magic # put32le (width header) # header # ct
   where
    header = mkHeader rs senderKeys ephemKeys fileInfo
```

Construction of the "file info blob" means we build the plaintext value:

>         {
>             fileKey: Key for file decryption (Base64),
>             fileNonce: Nonce for file decryption (Base64),
>             fileHash: BLAKE2 hash (32 bytes) of the ciphertext bytes. (Base64)
>         }

```cryptol
  // The triple of Key and nonce protecting the file along with the file's hash
  type FileInfo     = ([32][8], [16][8], [32][8])
  type FileInfoBlob = [155][8]

  mkFileInfoBlob : FileInfo
                -> FileInfoBlob
  mkFileInfoBlob (key,nonce,hash) =
      brace(
          jsonPair "fileKey"   (quote64 key)     # "," #
          jsonPair "fileNonce" (quote64 nonce) # "," #
          jsonPair "fileHash"  (quote64 hash)
      )
```

The header includes the public ephemeral key, version, and NrRecip copies of the
fileinfo inside a decryptInfo field as such:

> version: Version of the miniLock protocol used for this file (Currently 1) (Number)
> ephemeral: Public key from ephemeral key pair used to encrypt decryptInfo object (Base64),
> decryptInfo: { nonce1 : { encryptedFileInfo }
>              , nonce2 : ...
>              , ...
>              }

```cryptol
  mkHeader : {nrRecip} (fin nrRecip, nrRecip >= 1)
            => [nrRecip](MinilockID,[24][8])
            -> (Private25519, Public25519)
            -> (Private25519, Public25519)
            -> FileInfoBlob
            -> [89 + (DecryptInfoSize+1) * nrRecip - 1][8]
  mkHeader rs senderKeys ephemKeys infoBlob =
      brace (
            jsonPair "version" "1" # ","
          # jsonPair "ephemeral" (quote64 ephemKeys.1) # ","
          # jsonPair "decryptInfo" (brace decInfoFull)
        )
   where
    ds = [ mkDecryptInfo senderKeys ephemKeys recvID recvNonce infoBlob  # "," | (recvID,recvNonce) <- rs ]
    // Drop the trailing comma
    decInfoFull = take `{back = min nrRecip 1} (join ds)

  // XXX return 'succ' for successful decode of the public id
  mkDecryptInfo :
                   (Private25519, Public25519)
                -> (Private25519, Public25519)
                -> MinilockID -> [24][8] -> FileInfoBlob -> [DecryptInfoSize][8]
  mkDecryptInfo senderKeys ephemKeys theirID nonce infoBlob = quote64 nonce # ":" # quote ct
   where
    ct        = encryptWith nonce (ephemKeys.0) theirPublic internals
    internals =   brace ( jsonPair "senderID"    (quote (encodeID senderKeys.1)) # ","
                        # jsonPair "recipientID" (quote theirID)                 # ","
                        # jsonPair "fileInfo"    (quote fileInfoCT)
                        )
    fileInfoCT  = encryptWith nonce (senderKeys.0) theirPublic infoBlob
    (succ,theirPublic) = decodeID theirID

  encryptWith : {n} (2^^64 >= 32 + n) => [24][8] -> Private25519 -> Public25519 -> [n][8] -> [Enc64 (n+16)][8]
  encryptWith nonce secret public pt = base64enc (crypto_box pt nonce public secret)

  type NrChunks ptBytes = ptBytes / (2^^20)
  type LastChunkSize ptBytes = ptBytes - (NrChunks ptBytes) * 2^^20
  type EncryptedBytes ptBytes = 4 + 16 + 256 + (NrChunks ptBytes) * ((2^^20) + 4 + 16) + 4 + 16 + LastChunkSize ptBytes

  type ChunkSize = 2^^20
  type Chunk = [ChunkSize][8]
  type FullChunks bytes = bytes / ChunkSize
  type Rem bytes = bytes - FullChunks bytes * ChunkSize

  mkChunks :  {bytes} ( fin bytes )
           => [bytes][8] -> ([FullChunks bytes]Chunk, [Rem bytes][8])
  mkChunks pt = (cs,last)
    where cs   = split (take `{front = FullChunks bytes * ChunkSize, back = Rem bytes} pt)
          last = drop `{FullChunks bytes * ChunkSize} pt
```

The above code used some custom utility functions, which appear below.

```cryptol
  put32le : [32] -> [4][8]
  put32le x = reverse (split x)

  put64le : [64] -> [8][8]
  put64le x = reverse (split x)

  quote : {m} (fin m) => [m][8] -> [m+2][8]
  quote m = "\"" # m # "\""

  brace : {m} (fin m) => [m][8] -> [m+2][8]
  brace m = "{" # m # "}"

  quote64 : {m} (fin m) => [m][8] -> [4*(m + (3 - m % 3) % 3)/3 + 2][8]
  quote64 m = quote (base64enc m)

  jsonPair : {m,n} (fin m) => [m][8] -> [n][8] -> [3+m+n][8]
  jsonPair m n = quote m # ":" # n

// Encrypt a file such that one recipient
// User: "example@example.com
// Pass: "some bears eat all the honey in the jar"
//
// Can decrypt.
test_lock fname cont = file
  where
  myPriv    = testPriv
  myPub     = testPub
  theirID   = testID
  ephemPriv = zero # "ephemeral Curve25519"
  ephemPub  = Curve25519 ephemPriv basePoint25519
  nonceA    = zero # "recip1 nonce"
  nonceF    = zero # "file   nonce"
  key       = zero # "file key"
  file      = minilock [(theirID,nonceA)] fname cont (myPriv,myPub) key nonceF (ephemPriv,ephemPub)

test_construction : [MiniLockBytes 1 13][8]
test_construction = test_lock "some_filename" "some contents"
```

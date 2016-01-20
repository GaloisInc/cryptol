# Minilock in Cryptol

[miniLock](https://minilock.io) is a low-barrier to use file encryption utility
based on the algorithms:

 * SCrypt
    - PBKDF2
    - HMAC-SHA512
 * Blake2s
 * Base64
 * Base58
 * CryptoBox
    - Salsa20
    - Curve25519
    - Poly1305

This example is a specification of miniLock file encryption in Cryptol including
all component algorithms as well as primitive JSON encoding to allow
inter-operability between the official miniLock written in JavaScript and files
produced by Cryptol.

# Use

To encrypt a file consider:

```
CRYPTOLPATH=`pwd`/prim cryptol File.md
```

Then use the `miniLock` function such as can be seen in `test_lock`:

```
miniLock [(theirID, nonceA)] filename contents (myPrivKey, myPubKey) key nonceF (ephemPriv, ephemPub)
```

Note SCrypt, and thus miniLock ID and key derivation from user passwords, is too
expensive for the Cryptol interpreter to compute on all but todays more powerful
computers.  The ID generation can be done using `mkID` from `Keys.cry`.

# License

Copyright (c) 2013-2016 Galois, Inc.
Distributed under the terms of the BSD3 license (see LICENSE file)

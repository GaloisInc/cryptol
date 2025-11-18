
ML-Style Modules for Cryptol
----------------------------

Iavor S. Diatchki

Galois Inc

15 January 2021

Modules
--------

* Cryptol uses a Haskell-style module system

* A *module* is for managing names, and may:

  - bring *entities* into scope via *imports*
  - define new entities via *declarations*
  - *export* entities that are in scope

Example
-------

```cryptol
module M where

  import A(b)     // Brings `b` in scope

  x = 2 * b       // Defines `x` (public)

  private
    y = x + x     // Defines `y` (private)
```


Parameterize Modules: Current Version
-----------------------------

:::::::::::::: {.columns}
::: {.column}
### Parameterized module:

```cryptol
module F where

  parameter
    type n : #
    type constraint
          (n >= 128)
    key : [n]


  f : [n] -> [n]
  f x = key ^ x
```
:::
::: {.column}
### Instantiation:

```cryptol
module I = F where
  type n = 256
  key    = 17
```
:::
::::::::::::::


Issues
------

Common complaints:

* Clunky
  - Many small files for instantiation modules

* Inflexible
  - Cannot split a large parameterized module
    into multiple files

* Repetition
  - Cannot name groups of parameters for reuse



The New Design
--------------

* Nested modules
* Signatures
* Functors
* Instantiation
* Syntactic sugar


Nested Modules
--------------

* New concept: module entities
* Introduced via new declarations
* Used through `open` (similar to `import`)
* Module names are managed like any other name

Example
-------
```cryptol
module A where
  x = 0x2            // defines `x`, a value

  module B where     // defines `B`, a module
    y = x + 1        // defines `y`, a value

  open B(y)          // uses `B`, brings `y` in scope
  z = 2 * y          // defines `z`, uses `y`
```

Signatures
----------

A named collection of module parameters:

```cryptol
signature S where
  type n : #
  type constraint (n >= 128)
  key : [n]
```

Signature names are controlled by the
module system like other declarations.

Functors
--------

Modules may be parameterized with a parameter declaration:
```cyrptol
module F where

  signature S     // Defines `S`, a signature
    type n : #

  parameter P : S // Uses `S`, brings `n` in scope

  f : [n] -> [n]
  f x = x
```

Note: `P` is *not* a normal name.


Instantiation
-------------

Another way to introduce a module entity:
```cryptol
module I where

  module Arg where
    type n = 256

  module A = F with { P = Arg }
```

Syntactic Sugar
---------------

* Omit parameter name (single parameter functors)
* Instantiate single parameter functors
* Anonymous modules (generative)
* Combined `parameter` and `signature`
* Combined declare and open


Example
-------
A use case we'd like to support

```cryptol
module F where
  parameter
    type n : #
    key : [n]

  f : [n] -> [n]
  f x = x ^ key

module G where
  import F where
    type n = 8
    key    = 0x23
```

Desugared
---------
```cryptol
module F where

  signature A1
    type n : #
    key : [n]

  parameter Default : A1

  f : [n] -> [n]
  f x = x ^ key

module G where

  module A2 where
    type n = 8
    key    = 0x23

  import F with { Default = A2 }
```



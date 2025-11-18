Overview
--------

We would like to extend Cryptol with two related, yet different features:

  1. The ability to declare abstract types and functions---these are
    declarations that introduce new names, but do not provide definitions.
    This is useful if we want to reason about uninterpreted functions,
    for example.  It may also be useful to combine this feature with a
    mechanism to instantiate abstract values with concrete implamentations:
    this might be useful for testing abstract theories,
    implementing language primitives or, more generally, providing a
    foreign function interface to Cryptol.

  2. The ability to parametrize modules by types and values.  This feature
    is similar to the first in that from the point of view of a module,
    the parameters are essentially abstract values, but there are significant
    differences as outlined below.

The main difference between the two features is in how they are instantiated,
and also how they interact with the module system.  In the first case,
instantiation is global, in the sense that it scopes over a collection
of modules.   The instantiation is specified outside the module system,
using a mechanism that is yet to be defined.   In the second case,
instantiation happens whenever a parametrized module is imported.  Also,
note that it makes sense (and is useful) to import abstract values declared
in module into another module.   This is not really the case for module
parameters.

Examples
--------

A module with abstract declarations:

    module Nat where

    abstract
      type Nat : *
      Z : Nat
      S : Nat -> Nat

      isZ  : Nat -> Bit
      pred : Nat -> Nat

    property
      incDiff x = S x != Z

A module with abstract declarations may be imported by other modules, and
the abstract declarations are used as usual:

    module Add where

    import Nat

    add : Nat -> Nat -> Nat
    add x y = if isZ x then y else S (add (pred x) y)

If we provide a mechanism to provide concrete implementations for `Nat`,
then the same implementation would be used in all modules importing `Nat`.
This is similar to how Backpack works in Haskell.

Here is how we'd define a parametrized module:

    module BlockCrypto where

    parameter
      type KeyWidth  : #
      prepKeyEncrypt : [KeyWidth] -> [KeyWidth]
      prepKeyDecrypt : [KeyWidth] -> [KeyWidth]

    encrypt : [KeyWidth] -> [64] -> [64]
    encrypt rawKey block =
      doSomething
        where
        key = prepKeyEncrypt rawKey

When checking this module we would use the declared types for the the
value parameters, and we would treat `KeyWidth` as an abstract type.

We also need a mechanism to constrain the type parameter.  For example,
it is quite common to need a numeric type parameter, but require that
it is finite:

    module BlockCrypto where

    parameter
      type KeyWidth : #
      type constraint (fin KeyWidth, KeyWidth >= 64)

In this example we add two constraints: the key width will be finite
and at least 64.   These constraints will be assumed while
type checking the module, and validated when the module is instantiated.





When importing a parametrized module one would have to provide concrete
values for the parameters:

    module SomeApp where

    import BlockCrypto as C
      where type KeyWidth = 256
            prepKeyEncrypt = fancyPrepKeyEncrypt
            prepKeyDecrypt = fancyPrepKeyDecrypt


    fancyPrepKeyEncrypt : [256] -> [256]
    fancyPrepKeyEncrypt = someImplementation

The names used to instantiate a module should not depend on anything imported
by the module (i.e., one should be able to remove the instantiated import
declaration, and values used to instantiate a module should still work).

Also, there is an interaction between parametrized modules and generative
type declarations, of which Cryptol currently only has one not very well
advertised form, namely `newtype`.  Consider, for example:

    module Word where

    parameter
      type Size : #

    newtype Word = Word [Size]

Then, we could use the module as follows:

    module ExampleOfUsingWord where

    import Word as Word256 where Size = 256
    import Word as Word16  where Size = 16

Clearly, we'd like the types `Word256.Word` and `Word16.Word` to be distinct.
However, if we import `Word` with parameter `256` in another module, the
result should be the same as `Word256.Word`.

As long as the parameters are always types, we should be able to figure out
if the instantiations are the same an thus figure out which imported
types are the same.  It is a little trickier to do so in the presence of
value parameters.   To work around this we propose the following restriction:
*parameters may be instantiated only be names, optionally applied to some
type arguments*.  So, for example `zero` instantiated with `2` may
be used as a module parameter, but `0x10 + 0x20` would not.
Note that literals are a special case of this schema because they
are just sugar for `number`.

With this restriction, the rule is that two module instantiations are the
same if they have the same parameters, where types are compared as usual,
and values are compared by name.  Here are some examples:

      module X where
      parameter
        type T : #
        val : [T]

      module Examples where
      import X as E1 where T = 256; val = someVal
      import X as E2 where T = 256; val = 0x00
      import X as E3 where T = 256; val = zero`{8}

In module `Examples` all instantiations of `X` are different because `val`
uses different names.  In particular, `E2` and `E3` are different even though
`val` is essentially given the same value.  Comparing names allows us to
avoid having to evaluate while checking, but more importantly it allows us
to deal with parameters that are functions, which are can't be easily compared
for equality.

Naming Instantiations
---------------------

If a module has quite a few parameters, it might be nice to allow to
name a specific instantiation which can then be used in many places.
For example, we could have a module implementing some parametrized algorithm,
but in a specific application we would always use a specific instance of
the algorithm.  One way to do this might be allow module like this:

    module SpecificAlg = GeneralAlg where

    import SomeModule(tweak_cipher)

    type A    = [128]   // State type
    type K    = [128]   // Key type
    type n    = [16]    // Block size
    type p    = 2       // Process 2 blocks at once
    tagAmount = 8     // Add this much tag at the end

    Cost = 8

    // tweak_cipher parameter is imported from another module

    Enc k t = ...   // This argument is defined locally


The idea here is that module `SpecificAlg` is a concrete instance
of `GeneralAlg`.  The declarations following the `where` keyword are
similar to an ordinary module, but in this form they are just there
to specify the instantiation of `GeneralAlg`.  In particular, the
body should have a name in scope for each parameter of `GeneralAlg`.
The body may contain other auxiliary declaratoins that are used
to define the instance but are not exported directly.

XXX: Design choice: we may want to insist that this kind of named instantiation
is the only way to instantiate modules.  If we do that, then the generativity
issues from the previous section become less important: each named instance
generates a fresh instance of everything, and one has to import the same module
if one wants to get the same types.  It is unclear if this kind of named
instantiation is too heavy-weight for modules that have only a couple of
simple parameters...

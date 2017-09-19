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
    foregin function interface to Cryptol.

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

    parameters
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

Question: perhaps we want to provide a mechanism to constrain the type
parameter?   For example, maybe we want to say that `KeyWidth` would be
at least `128`?

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

    parameters
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
Note that literals are a special case of this schema becuase they
are just sugar for `demote`.

With this restriction, the rule is that two module instantiations are the
same if the havey the same parameters, where types are compared as usual,
and values are compared by name.  Here are some examples:

      moudle X where
      parameters
        type T : #
        val : [T]

      module Examples where
      import X as E1 where T = 256; val = someVal
      import X as E2 where T = 256; val = 0x00
      import X as E3 where T = 256; val = zero`{8}

In module `Examples` all instantiations of `X` are different because `val`
uses different names.  In particular, `E2` and `E3` are different even though
`val` is essentially given the same value.  Comparing names allows us to
avoid having to evalute while checking, but more importantly it allows us
to deal with parameters that are functions, which are can't be easily compared
for equality.















































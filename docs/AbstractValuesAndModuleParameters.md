Abstract Blocks
---------------

Abstract block contain signatures for operations but no implmenetations.
For example:

    module MyModule where

    abstract
      type T : *
      empty  : T
      op     : T -> T -> T

    property
      unitL x = op empty x == x
      unitR x = op x empty == x
      assoc x y z = op x (op y z) == op (op x y) z

    twice : T -> T
    twice x = op x x

[XXX] Question: do we want need a mechanism to provide some constraints
on the type `T`?  For example, that we don't know what `T` is but we
would like to assume that it is a member of `Arith`.

Expressions that depend on abstract values or types can be used in proofs
but not evaluated directly as the abstract declarations have no definitions.

It should be possible, however, to instantiate the abstract values to concrete
ones, resulting in a new executable module.  To do so, for each type, we
need to provide a ground type (i.e., a type with no free variables),
and for each abstract value we need to provide an instantiatation, which
may be either a literal constant, or a (possibly type instantiated) name of
a concrete value.

We avoid instantiating values with aribtrary expressions, because we would
like to be able to determine if two instantiations of a module are the same.
This enables us to have an "applicative" semantics for instantiations---
if a module is instantiate with equal arguments, the resulting module
would be the same.

Note that instantiation arguments would be considered the same, as long
as the types match, and the names match.  However, modules instantiated
with different names would be considered different, even if those names
denote values that are equal.  This is neccessary so that we can determine
if modules are the same, without having to evaluate them.


A module may be instantiated when it is imported into another module:

    module SomeModule where

    import MyModule as Qual
      using T     = [8]       // Ground type
            empty = zero      // really: zero `{[8]}
            op    = (+)       // really: (+)  `{[8]}

To avoid strange dependencies, the names used to instantiate a module
should be defined in imported modules. XXX: Perhaps it would be possible
to lift this restriction, and allow dependencies on definitions in this
module, as long as these definitions do not depend on the the instantiated
module at all.
















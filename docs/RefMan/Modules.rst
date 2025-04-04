Modules
=======

A *module* is used to group related definitions.  Each file may
contain at most one top-level module.

.. code-block:: cryptol

  module M where

  type T = [8]

  f : [8]
  f = 10

Module names should avoid using two consecutive underscores, because
those are used to generate names for various anonymous modules.


Hierarchical Module Names
-------------------------

Modules may have either simple or *hierarchical* names.
Hierarchical names are constructed by gluing together ordinary
identifiers using the symbol ``::``.

.. code-block:: cryptol

  module Hash::SHA256 where

  sha256 = ...

The structure in the name may be used to group together related
modules. The Cryptol implementation uses the structure of the
name to locate the file containing the module definition.
For example, when searching for module ``Hash::SHA256``, Cryptol
will look for a file named ``SHA256.cry`` in a directory called
``Hash``, contained in one of the directories specified by ``CRYPTOLPATH``.


Module Imports
--------------

To use the definitions from one module in another module, we use
``import`` declarations:


.. code-block:: cryptol
  :caption: module M

  // Provide some definitions
  module M where

  f : [8]
  f = 2


.. code-block:: cryptol
  :caption: module N

  // Uses definitions from `M`
  module N where

  import M  // import all definitions from `M`

  g = f   // `f` was imported from `M`


Import Lists
~~~~~~~~~~~~

Sometimes, we may want to import only some of the definitions
from a module.  To do so, we use an import declaration with
an *import list*.

.. code-block:: cryptol

  module M where

  f = 0x02
  g = 0x03
  h = 0x04

.. code-block:: cryptol

  module N where

  import M(f,g)  // Imports only `f` and `g`, but not `h`

  x = f + g

Using explicit import lists helps reduce name collisions.
It also tends to make code easier to understand,  because
it makes it easy to see the source of definitions.


Hiding Imports
~~~~~~~~~~~~~~

Sometimes a module may provide many definitions, and we want to use
most of them but with a few exceptions (e.g., because those would
result to a name clash).   In such situations it is convenient
to use a *hiding* import:

.. code-block:: cryptol
  :caption: module M

  module M where

  f = 0x02
  g = 0x03
  h = 0x04


.. code-block:: cryptol
  :caption: module N

  module N where

  import M hiding (h) // Import everything but `h`

  x = f + g



Qualified Module Imports
~~~~~~~~~~~~~~~~~~~~~~~~

Another way to avoid name collisions is by using a
*qualified* import.

.. code-block:: cryptol
  :caption: module M

  module M where

  f : [8]
  f = 2


.. code-block:: cryptol
  :caption: module N

  module N where

  import M as P

  g = P::f
  // `f` was imported from `M`
  // but when used it needs to be prefixed by the qualifier `P`

Qualified imports make it possible to work with definitions
that happen to have the same name but are defined in different modules.

Qualified imports may be combined with import lists or hiding clauses:

.. code-block:: cryptol
  :caption: Example

  import A as B (f)         // introduces B::f
  import X as Y hiding (f)  // introduces everything but `f` from X
                            // using the prefix `X`

It is also possible to use the same qualifier prefix for imports
from different modules.  For example:

.. code-block:: cryptol
  :caption: Example

  import A as B
  import X as B

Such declarations will introduces all definitions from ``A`` and ``X``
but to use them, you would have to qualify using the prefix ``B::``.


Private Blocks
--------------

In some cases, definitions in a module might use helper
functions that are not intended to be used outside the module.
It is good practice to place such declarations in *private blocks*:

.. code-block:: cryptol
  :caption: Private blocks

  module M where

  f : [8]
  f = 0x01 + helper1 + helper2

  private

    helper1 : [8]
    helper1 = 2

    helper2 : [8]
    helper2 = 3

The private block only needs to be indented if it might be followed by
additional public declarations.   If all remaining declarations are to be
private then no additional indentation is needed as the ``private`` block will
extend to the end of the module.

.. code-block:: cryptol
  :caption: Private blocks

  module M where

  f : [8]
  f = 0x01 + helper1 + helper2

  private

  helper1 : [8]
  helper1 = 2

  helper2 : [8]
  helper2 = 3


The keyword ``private`` introduces a new layout scope, and all declarations
in the block are considered to be private to the module.  A single module
may contain multiple private blocks.  For example, the following module
is equivalent to the previous one:

.. code-block:: cryptol
  :caption: Private blocks

  module M where

  f : [8]
  f = 0x01 + helper1 + helper2

  private
    helper1 : [8]
    helper1 = 2

  private
    helper2 : [8]
    helper2 = 3


Nested Modules
--------------

Module may be declared within other modules, using the ``submodule`` keword.

.. code-block:: cryptol
  :caption: Declaring a nested module called N

  module M where

    x = 0x02

    submodule N where
      y = x + 2

Submodules may refer to names in their enclosing scope.
Declarations in a sub-module will shadow names in the outer scope.

Declarations in a submodule may be imported with ``import submodule``,
which works just like an ordinary import except that ``X`` refers
to the name of a submodule.


.. code-block:: cryptol
  :caption: Using declarations from a submodule.

  module M where

    x = 0x02

    submodule N where
      y = x + 2

    import submodule N as P

    z = 2 * P::y

Note that recursive definitions across modules are not allowed.
So, in the previous example, it would be an error if ``y`` was
to try to use ``z`` in its definition.



Implicit Imports
~~~~~~~~~~~~~~~~

For convenience, we add an implicit qualified submodule import for
each locally defined submodules.

.. code-block:: cryptol
  :caption: Making use of the implicit import for a submodule.

  module M where

    x = 0x02

    submodule N where
      y = x + 2

    z = 2 * N::y

``N::y`` works in the previous example because Cryptol added
an implicit import ``import submodule N as N``.


Managing Module Names
~~~~~~~~~~~~~~~~~~~~~

The names of nested modules are managed by the module system just
like the name of any other declaration in Cryptol.  Thus, nested
modules may be declared in the public or private sections of their
containing module, and must be imported before they can be used.
Thus, to use a submodule defined in top-level module ``A`` into
another top-level module ``B`` requires two steps:

  1. First we need to import ``A`` to bring the name of the submodule in scope,
  2. Then we need to import the submodule to bring the names defined in it in scope.

.. code-block:: cryptol
  :caption: Using a nested module from a different top-level module.

  module A where

    x = 0x02

    submodule N where
      y = x + 2

  module B where
    import A            // Brings `N` in scope
    import submodule N  // Brings `y` in scope
    z = 2 * y


Parameterized Modules
---------------------

Interface Modules
~~~~~~~~~~~~~~~~~

An *interface module* describes the content of a module
without providing a concrete implementation.

.. code-block:: cryptol
  :caption: An interface module.

  interface module I where

    type n : #      // `n` is a numeric type

    type constraint (fin n, n >= 1)
                    // Assumptions about the declared numeric type

    x : [n]         // A declarations of a constant

Like other modules, interface modules may be nested in
other modules:

.. code-block:: cryptol
  :caption: A nested interface module

  module M where

    interface submodule I where

      type n : #      // `n` is a numeric type

      type constraint (fin n, n >= 1)
                      // Assumptions about the declared numeric type

      x : [n]         // A declarations of a constant

Interface modules may contain ``type`` or ``type constraint`` synonyms:

.. code-block:: cryptol
  :caption: A nested interface module

  interface module I where

    type n : #      // `n` is a numeric type

    type W = [n]    // A type synonym, available when the interface is imported

    type constraint (fin n, n >= 1)
                    // Assumptions about the declared numeric type

    x : W           // A declarations of a constant;  uses type synonym.




Importing an Interface Module
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A module may be parameterized by importing an interface,
instead of a concrete module

.. code-block:: cryptol
  :caption: A parameterized module

  // The interface desribes the parmaeters
  interface module I where
    type n : #
    type constraint (fin n, n >= 1)
    x : [n]


  // This module is parameterized
  module F where
    import interface I

    y : [n]
    y = x + 1

To import a nested interface use ``import interface sumbodule I``
and make sure that ``I`` is in scope.

It is also possible to import multiple interface modules,
or the same interface module more than once. Each import
of an interface module maybe be linked to a different concrete
module, as described in :ref:`instantiating_modules`.


.. code-block:: cryptol
  :caption: Multiple interface parameters

  interface module I where
    type n : #
    type constraint (fin n, n >= 1)
    x : [n]


  module F where
    import interface I as I
    import interface I as J

    y : [I::n]
    y = I::x + 1

    z : [J::n]
    z = J::x + 1

A parameterized module is also called a *functor*, in the tradition
of module parameterization in languages like Standard ML and OCaml.


    
Interface Constraints
~~~~~~~~~~~~~~~~~~~~~

When working with multiple interfaces, it is to useful
to be able to impose additional constraints on the
types imported from the interface.

.. code-block:: cryptol
  :caption: Adding constraints to interface parameters

  interface module I where
    type n : #
    type constraint (fin n, n >= 1)
    x : [n]


  module F where
    import interface I as I
    import interface I as J

    interface constraint (I::n == J::n)

    y : [I::n]
    y = I::x + J::x

In this example we impose the constraint that ``n``
(the width of ``x``) in both interfaces must be the
same.  Note that, of course, the two instantiations
may provide different values for ``x``.


.. _instantiating_modules:


Instantiating a Parameterized Module
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To use a parameterized module we need to provide concrete
implementations for the interfaces that it uses, and provide
a name for the resulting module.  This is done as follows:

.. code-block:: cryptol
  :caption: Instantiating a parameterized module using a single interface.

  interface module I where
    type n : #
    type constraint (fin n, n >= 1)
    x : [n]

  module F where
    import interface I

    y : [n]
    y = x + 1

  module Impl where
    type n = 8
    x = 26

  module MyF = F { Impl }

Here we defined a new module called ``MyF`` which is
obtained by filling in module ``Impl`` for the interface
used by ``F``.

If a module is parameterized my multiple interfaces
we need to provide an implementation module for each
interface, using a slight variation on the previous notation.

.. code-block:: cryptol
  :caption: Instantiating a parameterized module by name.

  // I is defined as above

  module F where
    import interface I as I
    import interface I as J

    interface constraint (I::n == J::n)

    y : [I::n]
    y = I::x + J::x

  module Impl1 where
    type n = 8
    x = 26

  module Impl2 where
    type n = 8
    x = 30

  module MyF = F { I = Impl1, J = Impl 2 }

Each interface import is identified by its name,
which is derived from the ``as`` clause on the
interface import.  If there is no ``as`` clause,
then the name of the parameter is derived from
the name of the interface itself.

Since interfaces are identified by name, the
order in which they are provided is not important.

Modules defined by instantiation may be nested,
just like any other module:

.. code-block:: cryptol
  :caption: Nested module instantiation.

  module M where

    import Somewhere // defines G

    submodule F = submodule G { I }

In this example, ``submodule F`` is defined
by instantiating some other parameterized
module ``G``, presumably imported from ``Somewhere``.
Note that in this case the argument to the instantiation
``I`` is a top-level module, because it is not
preceded by the ``submodule`` keyword.

To pass a nested module as the argument of a function,
use ``submodule I`` like this:

.. code-block:: cryptol
  :caption: Nested module instantiation.

  module M where

    import Somewhere // defines G and I

    submodule F = submodule G { submodule I }




Anonymous Interface Modules
~~~~~~~~~~~~~~~~~~~~~~~~~~~

If we need to just parameterize a module by a couple of types/values,
it is quite cumbersome to have to define a whole separate interface module.
To make this more convenient we provide the following notation for defining
an anonymous interface and using it straight away:

.. code-block:: cryptol
  :caption: Simple parameterized module.

  module M where

    parameter
      type n : #
      type constraint (fin n, n >= 1)
      x : [n]

    f : [n]
    f = 1 + x

The ``parameter`` block defines an interface module and uses it.
Note that the parameters may not use things defined in ``M`` as
the interface is declared outside of ``M``.  The ``parameter``
may contain the same sort of declarations that may appear in interfaces.

For external tools interacting with Cryptol, the name of the anonymous
parameter interface for module ``M`` is ``M__parameter`` (note that there
are 2 underscores after the name).


Anonymous Instantiation Arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes it is also a bit cumbersome to have to define a whole
separate module just to pass it as an argument to some parameterized
module.   To make this more convenient we support the following notation
for instantiating a module:

.. code-block:: cryptol

  // A parameterized module
  module M where

    parameter
      type n : #
      x      : [n]
      y      : [n]

    f : [n]
    f = x + y


  // A module instantiation
  module N = M
    where
    type n = 32
    x      = 11
    y      = helper

    helper = 12

The declarations in the ``where`` block are treated as the
definition of an anonymous module which is passed as the argument
to parameterized module ``M``.

For external tools interacting with Cryptol, the name of the anonymous
module actually passed to the functor is as follows:

  * ``N__where``, if ``N`` is a top-level module
  * ``where__at_l_c``, if ``N`` is a submodule

In the second form ``l`` and ``c`` are the line and column of ``N``.
If ``c`` is 1, then it is omitted, and the name will be just ``where__at_l``.
Note that in both cases the anonymous name contains two underscores next
to each other.



Anonymous Import Instantiations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We provide syntactic sugar for importing and instantiating a functor
at the same time:

.. code-block:: cryptol

  submodule F where
    parameter
      x : [8]
    y = x + 1

  import submodule F where
    x = 2

The ``where`` block may is the same as the ``where`` block in
expressions:  you may define type synonyms and values, but nothing else
(e.g., no ``newtype``).

It is also possible to import and instantiate a functor with an existing module
like this:

.. code-block:: cryptol

  submodule F where
    parameter
      x : [8]
    y = x + 1

  submodule G where
    x = 7

  import submodule F { submodule G }


Semantically, instantiating imports declare a local nested module and
import it.  For example, the ``where`` import above is equivalent
to the following declarations:

.. code-block:: cryptol

  submodule F where

    parameter
      x : [8]

    y = x + 1


  submodule M where
    x = 2


  submodule N = submodule F { submodule M }


  import submodule N

For external tools interacting with Cryptol, the name of the anonymous
module used in the import (the ``N`` in the above example) is of the form
``import_at__l_c``, where ``l`` and ``c`` are the line and column of the
``import`` keyword.  If the column is 1, then it is omitted, and the name
is of the form ``import_at__l``.  Note that the name contains two underscores
next to each other.


Passing Through Module Parameters
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Occasionally it is useful to define a functor that instantiates *another*
functor using the same parameters as the functor being defined
(i.e., a functor parameter is passed on to another functor).  This can
be done by using the keyword ``interface`` followed by the name of a parameter
in an instantiation.  Here is an example:

.. code-block:: cryptol

  interface submodule S where
    x : [8]

  // A functor, parameterized on S
  submodule G where
    import interface submodule S
    y = x + 1

  // Another functor, also parameterize on S
  submodule F where
    import interface submodule S as A

    // Instantiate `G` using parameter `A` of `F`
    import submodule G { interface A }    // Brings `y` in scope

    z = A::x + y

  // Brings `z` into scope: z = A::x + y
  //                          = 5    + (5 + 1)
  //                          = 11
  import submodule F where
    x = 5


Instantiation by Parametrizing Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is also possible to instantiate a functor parameter *without* providing
an implementation module.  Instead, the declarations in the instantiated
module all get additional parameters corresponding to the functor's parameters.
This is done by providing ``_`` as the parameter to a functor:

.. code-block:: cryptol
  :caption: Instantiation by Parametrizing Declarations

  submodule F where
    parameter
      type n : #
      x : [n]

    f : (fin n) => [n] -> [n]
    f v = v + x

  submodule M = submodule F { _ }
  import submodule M as M

This example defines module ``M`` by instantiating ``F`` without
a parameter.  Here is the resulting type of ``f``:

.. code-block::

  Main> :t M::f
  M::f : {n} (fin n) => {x : [n]} -> [n] -> [n]

Note that ``f`` has a new type parameter ``n``, and a new value parameter
of a record type.  The type parameter ``n`` corresponds to the functor's
type parameter while the record parameter has one field for each value
parameter of the functor.

.. warning::

  The order in which type parameters are added to a declaration is not
  specified, so you'd have to use a *named* type application to apply
  a type explicitly.

Functors with multiple parameters may use ``_`` as argument for more
than one parameter, and may also provide implementations for some of
the parameters and use ``_`` for others.

**[Parameter Names]** The names of the parameters in the declarations
are the same as the names that are in scope, unless a parameter came
in through a qualified interface import (i.e., the interface import
uses the ``as`` clause).  In the case the name of the parameter is
computed by replacing the ``::`` with ``'`` because ``::`` may not appear
in type parameters or record fields.  For example, if a module had
a parameter ``I::x``, then its ``_`` instantiation will use a
record with a field named ``I'x``.

**[Restrictions]** There are some restrictions on functor parameters
that can be defined with ``_``:

  * The functor should not contain other functors nested in it.
    This is because it is unclear how to parameterize the parameters of
    nested functors.

  * All values coming through ``_`` parameters should have simple
    (i.e., non-polymorphic) types.  This is because Cryptol does not
    support records with polymorphic fields.

  * All types and values coming through ``_`` parameters should have
    distinct names.  This is because the fields in the record and
    type names use labels derived. Generally this should not be a
    problem unless a functor defined some parameters that have
    ``'`` in the middle.


**[Backtick Imports]** For backward compatibility, we also provide
syntactic sugar for importing a functor with a single interface parameter
and instantiating it:

.. code-block:: cryptol
  :caption: Backtick Import

  submodule F where
    parameter
      type n : #
      x : [n]

    f : (fin n) => [n] -> [n]
    f v = v + x

  import submodule `F

This is equivalent to writing:

.. code-block:: cryptol

  import submodule F { _ }

This, in turn, is syntactic sugar for creating an anonymous module:

.. code-block:: cryptol

  submodule M = F { _ }
  import submodule M










Modules
=======

A *module* is used to group some related definitions.  Each file may
contain at most one top-level module.

.. code-block:: cryptol

  module M where

  type T = [8]

  f : [8]
  f = 10


Hierarchical Module Names
-------------------------

Module may have either simple or *hierarchical* names.
Hierarchical names are constructed by gluing together ordinary
identifiers using the symbol ``::``.

.. code-block:: cryptol

  module Hash::SHA256 where

  sha256 = ...

The structure in the name may be used to group together related
modules.  Also, the Cryptol implementation uses the structure of the
name to locate the file containing the definition of the module.
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

Module may be declared withing other modules, using the ``submodule`` keword.

.. code-block:: cryptol
  :caption: Declaring a nested module called N

  module M where

    x = 0x02

    submodule N where
      y = x + 2

Submodules may refer to names in their enclosing scope.
Declarations in a sub-module will shadow names in the outer scope.

Declarations in a submdule may be imported with ``import submodule``,
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
an implicit import ``import submoulde N as N``.


Managing Module Names
~~~~~~~~~~~~~~~~~~~~~

The names of nested modules are managed by the module system just
like the name of any other declaration in Cryptol.  Thus, nested
modules may declared in the public or private sections of their
containing module, and need to be imported before they can be used.
Thus, to use a submodule defined in top-level module ``A`` into
another top-level module ``B`` requires two steps:

  1. First we need to import ``A`` to bring the name of the submodule in scope
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

Like other modules, interfaces modules may be nested in
other modules:

.. code-block:: cryptol
  :caption: A nested interface module

  module M where

    interface submodule I where

      type n : #      // `n` is a numeric type

      type constraint (fin n, n >= 1)
                      // Assumptions about the declared numeric type

      x : [n]         // A declarations of a constant


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
or the same interface module more than once.   Each import
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
the interface is declared outside of ``M``.


Anonymous Instantiation Arguments
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Sometimes it is also a bit cumbersome to have to define a whole
separate module just to pass it as an argument to some parameterized
module.   To make this more convenient we support the following notion
for instantiation a module:

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



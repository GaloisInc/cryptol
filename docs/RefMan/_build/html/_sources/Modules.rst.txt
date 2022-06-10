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
private then no additional indentation is needed as the `private` block will
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



Parameterized Modules
---------------------

.. warning::
  This section documents the current design, but we are in the process of
  redesigning some aspects of the parameterized modules mechanism.


.. code-block:: cryptol

  module M where

  parameter
    type n : #              // `n` is a numeric type parameter

    type constraint (fin n, n >= 1)
      // Assumptions about the parameter

    x : [n]                 // A value parameter

  // This definition uses the parameters.
  f : [n]
  f = 1 + x


Named Module Instantiations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One way to use a parameterized module is through a named instantiation:

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
  module N = M where

  type n = 32
  x      = 11
  y      = helper

  helper = 12

The second module, ``N``, is computed by instantiating the parameterized
module ``M``.  Module ``N`` will provide the exact same definitions as ``M``,
except that the parameters will be replaced by the values in the body
of ``N``.   In this example, ``N`` provides just a single definition, ``f``.

Note that the only purpose of the body of ``N`` (the declarations
after the ``where`` keyword) is to define the parameters for ``M``.


Parameterized Instantiations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is possible for a module instantiation to be itself parameterized.
This could be useful if we need to define some of a module's parameters
but not others.

.. code-block:: cryptol

  // A parameterized module
  module M where

  parameter
    type n : #
    x      : [n]
    y      : [n]

  f : [n]
  f = x + y


  // A parameterized instantiation
  module N = M where

  parameter
    x : [32]

  type n = 32
  y      = helper

  helper = 12

In this case ``N`` has a single parameter ``x``.  The result of instantiating
``N`` would result in instantiating ``M`` using the value of ``x`` and ``12``
for the value of ``y``.


Importing Parameterized Modules
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

It is also possible to import a parameterized module without using
a module instantiation:

.. code-block:: cryptol

  module M where

  parameter
    x : [8]
    y : [8]

  f : [8]
  f = x + y

.. code-block:: cryptol

  module N where

  import `M

  g = f { x = 2, y = 3 }

A *backtick* at the start of the name of an imported module indicates
that we are importing a parameterized module.  In this case, Cryptol
will import all definitions from the module as usual, however every
definition will have some additional parameters corresponding to
the parameters of a module.  All value parameters are grouped in a record.

This is why in the example ``f`` is applied to a record of values,
even though its definition in ``M`` does not look like a function.




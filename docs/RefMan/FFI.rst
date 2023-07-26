Foreign Function Interface
==========================

The foreign function interface (FFI) allows Cryptol to call functions written in
C (or other languages that use the C calling convention).

Platform support
----------------

The FFI is built on top of the C ``libffi`` library, and as such, it should be
portable across many operating systems. We have tested it to work on Linux,
macOS, and Windows.

Basic usage
-----------

Suppose we want to implement the following function in C:

.. code-block:: cryptol

  add : [32] -> [32] -> [32]

In our Cryptol file, we declare it as a ``foreign`` function with no body:

.. code-block:: cryptol

  foreign add : [32] -> [32] -> [32]

Then we write the following C function:

.. code-block:: c

  uint32_t add(uint32_t x, uint32_t y) {
    return x + y;
  }

Cryptol can generate a C header file containing the appropriate function
prototypes given the corresponding Cryptol ``foreign`` declarations with the
``:generate-foreign-header`` command. You can then ``#include`` the generated
header file in your C file to help write the C implementation.

.. code-block::

  Cryptol> :generate-foreign-header Example.cry
  Loading module Example
  Writing header to Example.h

The C code must first be compiled into a dynamically loaded shared library. When
Cryptol loads the module containing the ``foreign`` declaration, it will look
for a shared library in the same directory as the Cryptol module, with the same
name as the Cryptol file but with a different file extension. The exact
extension it uses is platform-specific:

* On Linux, it looks for the extension ``.so``.
* On macOS, it looks for the extension ``.dylib``.
* On Windows, it looks for the extension ``.dll``.

For example, if you are on Linux and your ``foreign`` declaration is in
``Foo.cry``, Cryptol will dynamically load ``Foo.so``. Then for each ``foreign``
declaration it will look for a symbol with the same name in the shared library.
So in this case the function we want to call must be bound to the symbol ``add``
in the shared library.

Once the module is loaded, the foreign ``add`` function can be called like any
other Cryptol function. Cryptol automatically converts between Cryptol ``[32]``
values and C ``uint32_t`` values.

The whole process would look something like this:

.. code-block::

  $ cc -fPIC -shared Example.c -o Example.so
  $ cryptol
  Loading module Cryptol
  Cryptol> :l Example.cry
  Loading module Cryptol
  Loading module Main
  Main> add 1 2
  0x00000003

Note: Since Cryptol currently only accesses the compiled binary and not the C
source, it has no way of checking that the Cryptol function type you declare in
your Cryptol code actually matches the type of the C function. It can generate
the correct C headers but if the actual implementation does not match it there
may be undefined behavior.

Compiling C code
----------------

Cryptol currently does not handle compilation of C code to shared libraries. For
simple usages, you can do this manually with the following commands:

* Linux: ``cc -fPIC -shared Foo.c -o Foo.so``
* macOS: ``cc -dynamiclib Foo.c -o Foo.dylib``
* Windows: ``cc -fPIC -shared Foo.c -o Foo.dll``

Converting between Cryptol and C types
--------------------------------------

This section describes how a given Cryptol function signature maps to a C
function prototype. The FFI only supports a limited set of Cryptol types which
have a clear translation into C.

This mapping can now be done automatically with the ``:generate-foreign-header``
command mentioned above; however, this section is still worth reading to
understand the supported types and what the resulting C parameters mean.

Overall structure
~~~~~~~~~~~~~~~~~

Cryptol ``foreign`` bindings must be functions. These functions may have
multiple (curried) arguments; they may also be polymorphic, with certain
limitations. That is, the general structure of a ``foreign`` declaration would
look something like this:

.. code-block:: cryptol

  foreign f : {a1, ..., ak} (c1, ..., cn) => T1 -> ... -> Tm -> Tr

Each type argument to the Cryptol function (``a1, ..., ak`` above) corresponds
to a value argument to the C function. These arguments are passed first, in the
order of the type variables declared in the Cryptol signature, before any
Cryptol value arguments.

Each value argument to the Cryptol function (``T1, ..., Tm`` above) corresponds
to a number of value arguments to the C function. That is, a Cryptol value
argument could correspond to zero, one, or many C arguments. The C arguments for
each Cryptol value argument are passed in the order of the Cryptol value
arguments, after any C arguments corresponding to Cryptol type arguments.

The return value of the Cryptol function (``Tr`` above) is either obtained by
directly returning from the C function or by passing *output arguments* to the C
function, depending on the return type. Output arguments are pointers to memory
which can be modified by the C function to store its output values. If output
arguments are used, they are passed last, after the C arguments corresponding to
Cryptol arguments.

The following tables list the C type(s) that each Cryptol type (or kind)
corresponds to.

Type parameters
~~~~~~~~~~~~~~~

============  ==========
Cryptol kind  C type
============  ==========
``#``         ``size_t``
============  ==========

Only numeric type parameters are allowed in polymorphic ``foreign`` functions.
Furthermore, each type parameter ``n`` must satisfy ``fin n``. This has to be
explicitly declared in the Cryptol signature.

Note that if a polymorphic foreign function is called with a type argument that
does not fit in a ``size_t``, there will be a runtime error. (While we could
check this statically by requiring that all type variables in foreign functions
satisfy ``< 2^^64`` instead of just ``fin``, in practice this would be too
cumbersome.)

Bit
~~~

============  ===========
Cryptol type  C type
============  ===========
``Bit``       ``uint8_t``
============  ===========

When converting to C, ``True`` is converted to ``1`` and ``False`` to ``0``.
When converting to Cryptol, any nonzero number is converted to ``True`` and
``0`` is converted to ``False``.

Bit Vector Types
~~~~~~~~~~~~~~~~

Let ``K : #`` be a Cryptol type. Note ``K`` must be an actual fixed numeric type
and not a type variable.

==================================  ============
Cryptol type                        C type
==================================  ============
``[K]Bit`` where ``0  <= K <= 8``   ``uint8_t``
``[K]Bit`` where ``8  <  K <= 16``  ``uint16_t``
``[K]Bit`` where ``16 <  K <= 32``  ``uint32_t``
``[K]Bit`` where ``32 <  K <= 64``  ``uint64_t``
==================================  ============

If the Cryptol type is smaller than the C type, then when converting to C the
value is padded with zero bits, and when converting to Cryptol the extra bits
are ignored. For instance, for the Cryptol type ``[4]``, the Cryptol value ``0xf
: [4]`` is converted to the C value ``uint8_t`` ``0x0f``, and the C ``uint8_t``
``0xaf`` is converted to the Cryptol value ``0xf : [4]``.

Note that bit vectors larger than 64 bits are not supported, since there is no
standard C integral type for that. You can split it into a sequence of smaller
words first in Cryptol, then use the FFI conversion for sequences of words to
handle it in C as an array.

Floating point types
~~~~~~~~~~~~~~~~~~~~

============  ==========
Cryptol type  C type
============  ==========
``Float32``   ``float``
``Float64``   ``double``
============  ==========

Note: the Cryptol ``Float`` types are defined in the built-in module ``Float``.
Other sizes of floating points are not supported.

Math Types
~~~~~~~~~~

Values of high precision types and ``Z`` are represented using the GMP library.

============  ==========
Cryptol type  C type
============  ==========
``Integer``   ``mpz_t``
``Rational``  ``mpq_t``
``Z n``       ``mpz_t``
============  ==========

Results of these types are returned in *output* parameters,
but since both ``mpz_t`` and ``mpz_q`` are already reference
types there is no need for an extra pointer in the result.
For example, a Cryptol function ``f : Integer -> Rational``
would correspond to a C function ``f(mpz_t in, mpq_t out)``.

All parameters passed to the C function (no matter if
input or output) are managed by Cryptol, which takes care
to call ``init`` before their use and ``clear`` after.


Sequences
~~~~~~~~~

Let ``n1, n2, ..., nk : #`` be Cryptol types (with ``k >= 1``), possibly
containing type variables, that satisfy ``fin n1, fin n2, ..., fin nk``, and
``T`` be one of the above Cryptol *bit vector types*, *floating point types*, or
*math types*.  Let ``U`` be the C type that ``T`` corresponds to.

====================  ===========
Cryptol type          C type
====================  ===========
``[n1][n2]...[nk]T``  ``U*``
====================  ===========

The C pointer points to an array of ``n1 * n2 * ... * nk`` elements of type
``U``. If the sequence is multidimensional, it is flattened and stored
contiguously, similar to the representation of multidimensional arrays in C.
Note that, while the dimensions of the array itself are not explicitly passed
along with the pointer, any type arguments contained in the size are passed as C
``size_t``'s earlier, so the C code can always know the dimensions of the array.

Tuples and records
~~~~~~~~~~~~~~~~~~

Let ``T1, T2, ..., Tn`` be Cryptol types supported by the FFI (which may be any
of the types mentioned above, or tuples and records themselves). Let
``U1, U2, ..., Un`` be the C types that ``T1, T2, ..., Tn`` respectively
correspond to. Let ``f1, f2, ..., fn`` be arbitrary field names.

=================================  ===================
Cryptol type                       C types
=================================  ===================
``(T1, T2, ..., Tn)``              ``U1, U2, ..., Un``
``{f1: T1, f2: T2, ..., fn: Tn}``  ``U1, U2, ..., Un``
=================================  ===================

In this case, each Cryptol tuple or record is flattened out; passing a tuple as
an argument behaves the same as if you passed its components individually. This
flattening is applied recursively for nested tuples and records. Note that this
means empty tuples don't map to any C values at all.

Type synonyms
~~~~~~~~~~~~~

All type synonyms are expanded before applying the above rules, so you can use
type synonyms in ``foreign`` declarations to improve readability.

Return values
~~~~~~~~~~~~~

If the Cryptol return type is ``Bit`` or one of the above *bit vector types* or
*floating point types*, the value is returned directly from the C function. In
that case, the return type of the C function will be the C type corresponding to
the Cryptol type, and no extra arguments are added.

If the Cryptol return type is one of the *math types*, a sequence, tuple,
or record, then the value is returned using output arguments,
and the return type of the C function will be ``void``.
For tuples and records, each component is recursively returned as
output arguments. When treated as an output argument, each C type ``U`` will be
a pointer ``U*`` instead, except in the case of *math types* and sequences,
where the output and input versions are the same type, because it is already a pointer.

Quick reference
~~~~~~~~~~~~~~~

==================================  ===================  =============  =========================
Cryptol type (or kind)              C argument type(s)   C return type  C output argument type(s)
==================================  ===================  =============  =========================
``#``                               ``size_t``           N/A            N/A
``Bit``                             ``uint8_t``          ``uint8_t``    ``uint8_t*``
``[K]Bit`` where ``0  <= K <= 8``   ``uint8_t``          ``uint8_t``    ``uint8_t*``
``[K]Bit`` where ``8  <  K <= 16``  ``uint16_t``         ``uint16_t``   ``uint16_t*``
``[K]Bit`` where ``16 <  K <= 32``  ``uint32_t``         ``uint32_t``   ``uint32_t*``
``[K]Bit`` where ``32 <  K <= 64``  ``uint64_t``         ``uint64_t``   ``uint64_t*``
``Float32``                         ``float``            ``float``      ``float*``
``Float64``                         ``double``           ``double``     ``double*``
``Integer``                         ``mpz_t``            N/A            ``mpz_t``
``Rational``                        ``mpq_t``            N/A            ``mpq_t``
``Z n``                             ``mpz_t``            N/A            ``mpz_t``
``[n1][n2]...[nk]T``                ``U*``               N/A            ``U*``
``(T1, T2, ..., Tn)``               ``U1, U2, ..., Un``  N/A            ``V1, V2, ..., Vn``
``{f1: T1, f2: T2, ..., fn: Tn}``   ``U1, U2, ..., Un``  N/A            ``V1, V2, ..., Vn``
==================================  ===================  =============  =========================

where ``K`` is a constant number, ``ni`` are variable numbers, ``Ti`` is a type,
``Ui`` is its C argument type, and ``Vi`` is its C output argument type.

Memory
------

When pointers are involved, namely in the cases of sequences and output
arguments, they point to memory. This memory is always allocated and deallocated
by Cryptol; the C code does not need to manage this memory.

For GMP types, Cryptol will call ``init`` and ``clear`` as needed.

In the case of sequences, the pointer will point to an array. In the case of an
output argument for a non-sequence type, the pointer will point to a piece of
memory large enough to hold the given C type, and you should not try to access
any adjacent memory.

For input sequence arguments, the array will already be set to the values
corresponding to the Cryptol values in the sequence. For output arguments, the
memory may be uninitialized when passed to C, and the C code should not read
from it. It must write to the memory the value it is returning.

Evaluation
----------

All Cryptol arguments are fully evaluated when a foreign function is called.

The FFI is intended to be used with pure functions that do not perform side
effects such as mutating global state, printing to the screen, interacting with
the file system, etc. Cryptol does not enforce this convention, however, so it
is possible to use impure functions from the FFI if you wish. Cryptol does not
make any guarantees about the order in which side effects will be executed, nor
does it make any guarantees about preserving any global state between
invocations of impure FFI functions.

Example
-------

The Cryptol signature

.. code-block:: cryptol

  foreign f : {n} (fin n) => [n][10] -> {a : Bit, b : [64]}
                             -> (Float64, [n + 1][20])

corresponds to the C signature

.. code-block:: c

  void f(size_t n, uint16_t *in0, uint8_t in1_a, uint64_t in1_b,
         double *out_0, uint32_t *out_1);

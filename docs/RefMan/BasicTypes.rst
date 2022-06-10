
Basic Types
===========


Tuples and Records
------------------

Tuples and records are used for packaging multiple values together.
Tuples are enclosed in parentheses, while records are enclosed in
curly braces.  The components of both tuples and records are separated by
commas.  The components of tuples are expressions, while the
components of records are a label and a value separated by an equal
sign.  Examples:

.. code-block:: cryptol

  (1,2,3)           // A tuple with 3 component
  ()                // A tuple with no components

  { x = 1, y = 2 }  // A record with two fields, `x` and `y`
  {}                // A record with no fields

The components of tuples are identified by position, while the
components of records are identified by their label, and so the
ordering of record components is not important for most purposes.
Examples:

.. code-block:: cryptol

             (1,2) == (1,2)               // True
             (1,2) == (2,1)               // False

  { x = 1, y = 2 } == { x = 1, y = 2 }    // True
  { x = 1, y = 2 } == { y = 2, x = 1 }    // True

Ordering on tuples and records is defined lexicographically. Tuple
components are compared in the order they appear, whereas record
fields are compared in alphabetical order of field names.



Accessing Fields
~~~~~~~~~~~~~~~~

The components of a record or a tuple may be accessed in two ways: via
pattern matching or by using explicit component selectors.  Explicit
component selectors are written as follows:

.. code-block:: cryptol

  (15, 20).0           == 15
  (15, 20).1           == 20

  { x = 15, y = 20 }.x == 15

Explicit record selectors may be used only if the program contains
sufficient type information to determine the shape of the tuple or
record.  For example:

.. code-block:: cryptol

  type T = { sign : Bit, number : [15] }

  // Valid definition:
  // the type of the record is known.
  isPositive : T -> Bit
  isPositive x = x.sign

  // Invalid definition:
  // insufficient type information.
  badDef x = x.f

The components of a tuple or a record may also be accessed using
pattern matching.  Patterns for tuples and records mirror the syntax
for constructing values: tuple patterns use parentheses, while record
patterns use braces.  Examples:

.. code-block:: cryptol

  getFst (x,_) = x

  distance2 { x = xPos, y = yPos } = xPos ^^ 2 + yPos ^^ 2

  f p = x + y where
      (x, y) = p

Selectors are also lifted through sequence and function types, point-wise,
so that the following equations should hold:

.. code-block:: cryptol

  xs.l == [ x.l | x <- xs ]     // sequences
  f.l  == \x -> (f x).l         // functions

Thus, if we have a sequence of tuples, ``xs``, then we can quickly obtain a
sequence with only the tuples' first components by writing ``xs.0``.

Similarly, if we have a function, ``f``, that computes a tuple of results,
then we can write ``f.0`` to get a function that computes only the first
entry in the tuple.

This behavior is quite handy when examining complex data at the REPL.




Updating Fields
~~~~~~~~~~~~~~~

The components of a record or a tuple may be updated using the following
notation:

.. code-block:: cryptol

  // Example values
  r = { x = 15, y = 20 }      // a record
  t = (True,True)             // a tuple
  n = { pt = r, size = 100 }  // nested record

  // Setting fields
  { r | x = 30 }          == { x = 30, y = 20 }
  { t | 0 = False }       == (False,True)

  // Update relative to the old value
  { r | x -> x + 5 }      == { x = 20, y = 20 }

  // Update a nested field
  { n | pt.x = 10 }       == { pt = { x = 10, y = 20 }, size = 100 }
  { n | pt.x -> x + 10 }  == { pt = { x = 25, y = 20 }, size = 100 }


Sequences
---------

A sequence is a fixed-length collection of elements of the same type.
The type of a finite sequence of length `n`, with elements of type `a`
is ``[n] a``.  Often, a finite sequence of bits, ``[n] Bit``, is called a
*word*.  We may abbreviate the type ``[n] Bit`` as ``[n]``.  An infinite
sequence with elements of type `a` has type ``[inf] a``, and ``[inf]`` is
an infinite stream of bits.

.. code-block:: cryptol

  [e1,e2,e3]            // A sequence with three elements

  [t1 .. t2]            // Enumeration
  [t1 .. <t2]           // Enumeration (exclusive bound)
  [t1 .. t2 by n]       // Enumeration (stride)
  [t1 .. <t2 by n]      // Enumeration (stride, ex. bound)
  [t1 .. t2 down by n]  // Enumeration (downward stride)
  [t1 .. >t2 down by n] // Enumeration (downward stride, ex. bound)
  [t1, t2 .. t3]        // Enumeration (step by t2 - t1)

  [e1 ...]              // Infinite sequence starting at e1
  [e1, e2 ...]          // Infinite sequence stepping by e2-e1

  [ e | p11 <- e11, p12 <- e12    // Sequence comprehensions
      | p21 <- e21, p22 <- e22 ]

  x = generate (\i -> e)    // Sequence from generating function
  x @ i = e                 // Sequence with index binding
  arr @ i @ j = e           // Two-dimensional sequence

Note: the bounds in finite sequences (those with `..`) are type
expressions, while the bounds in infinite sequences are value
expressions.

.. table:: Sequence operations.

  +------------------------------+---------------------------------------------+
  | Operator                     | Description                                 |
  +==============================+=============================================+
  |   ``#``                      | Sequence concatenation                      |
  +------------------------------+---------------------------------------------+
  |   ``>>``  ``<<``             | Shift (right, left)                         |
  +------------------------------+---------------------------------------------+
  |   ``>>>`` ``<<<``            | Rotate (right, left)                        |
  +------------------------------+---------------------------------------------+
  |   ``>>$``                    | Arithmetic right shift (on bitvectors only) |
  +------------------------------+---------------------------------------------+
  |   ``@`` ``!``                | Access elements (front, back)               |
  +------------------------------+---------------------------------------------+
  |   ``@@`` ``!!``              | Access sub-sequence (front, back)           |
  +------------------------------+---------------------------------------------+
  |   ``update`` ``updateEnd``   | Update the value of a sequence at           |
  |                              | a location                                  |
  |                              | (front, back)                               |
  +------------------------------+---------------------------------------------+
  |   ``updates`` ``updatesEnd`` | Update multiple values of a sequence        |
  |                              | (front, back)                               |
  +------------------------------+---------------------------------------------+


There are also lifted pointwise operations.

.. code-block:: cryptol

  [p1, p2, p3, p4]          // Sequence pattern
  p1 # p2                   // Split sequence pattern


Functions
---------

.. code-block:: cryptol

  \p1 p2 -> e              // Lambda expression
  f p1 p2 = e              // Function definition



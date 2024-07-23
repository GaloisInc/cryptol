
Basic Syntax
============


Declarations
------------

.. code-block:: cryptol

  f x = x + y + z


Type Signatures
---------------

.. code-block:: cryptol

  f,g : {a,b} (fin a) => [a] b


Numeric Constraint Guards
-------------------------

A declaration with a signature can use *numeric constraint guards*,
which are used to change the behavior of a functoin depending on its
numeric type parameters.  For example:

.. code-block:: cryptol

  len : {n} (fin n) => [n]a -> Integer
  len xs | n == 0 => 0
         | n >  0 => 1 + len (drop `{1} xs)

Each behavior starts with ``|`` and lists some constraints on the numeric
parameters to a declaration.  When applied, the function will use the first
definition that satisfies the provided numeric parameters.

Numeric constraint guards are quite similar to an ``if`` expression,
except that decisions are based on *types* rather than values.  There
is also an important difference to simply using demotion and an
actual ``if`` statement:

.. code-block:: cryptol
  
  len' : {n} (fin n) => [n]a -> Integer
  len' xs = if `n == 0 => 0
             | `n >  0 => 1 + len (drop `{1} xs)

The definition of ``len'`` is rejected, because the *value based* ``if``
expression does provide the *type based* fact ``n >= 1`` which is
required by ``drop `{1} xs``, while in ``len``, the type-checker
locally-assumes the constraint ``n > 0`` in that constraint-guarded branch
and so it can in fact determine that ``n >= 1``.

Requirements:
  - Numeric constraint guards only support constraints over numeric literals,
    such as ``fin``, ``<=``, ``==``, etc.
    Type constraint aliases can also be used as long as they only constrain
    numeric literals.
  - The numeric constraint guards of a declaration should be exhaustive. The
    type-checker will attempt to prove that the set of constraint guards is
    exhaustive, but if it can't then it will issue a non-exhaustive constraint
    guards warning. This warning is controlled by the environmental option
    ``warnNonExhaustiveConstraintGuards``.
  - Each constraint guard is checked *independently* of the others, and there
    are no implict assumptions that the previous behaviors do not match---
    instead the programmer needs to specify all constraints explicitly
    in the guard.

Layout
------

Groups of declarations are organized based on indentation.
Declarations with the same indentation belong to the same group.
Lines of text that are indented more than the beginning of a
declaration belong to that declaration, while lines of text that are
indented less terminate a group of declarations.  Consider, for example,
the following Cryptol declarations:

.. code-block:: cryptol

  f x = x + y + z
    where
    y = x * x
    z = x + y

  g y = y

This group has two declarations, one for `f` and one for `g`.  All the
lines between `f` and `g` that are indented more than `f` belong to
`f`.  The same principle applies to the declarations in the ``where`` block
of `f`, which defines two more local names, `y` and `z`.



Comments
--------

Cryptol supports block comments, which start with ``/*`` and end with
``*/``, and line comments, which start with ``//`` and terminate at the
end of the line.  Block comments may be nested arbitrarily.

.. code-block:: cryptol

  /* This is a block comment */
  // This is a line comment
  /* This is a /* Nested */ block comment */

Documentation Comments
----------------------

Declarations in Cryptol can have documentation attached to them using special
*docstring* comments. These attached comments are accessible in the REPL
using the ``:help`` command.

Syntactically, docstring comments are block comments that start with exactly
two ``*`` characters: ``/** ... */``. For lines after the first line a common
prefix of whitespace and asterisks will be stripped in order to support
stylistic blocks. Whitespace between the last asterisk on a line and the
end-of-line can be dropped without affecting prefix detection.

.. code-block:: cryptol
  :caption: Examples of docstrings

  /** Example documentation for x */
  x = 1

  /**
    Example documentation for y
   */
  y = 1

  /**
   * Example documentation
   * for z
   */
  z = 1

Test cases can be included in docstring comments that will be checked
by the ``:check-docstrings`` command in the form of code blocks that are
unlabeled or labeled with the ``repl`` language. This cases should be
in the form of REPL commands. Success of the test is defined to be the
success of all the REPL commands.

.. code-block:: cryptol
  :caption: Example docstring with checked test

  /** This function 
   *
   * ```repl
   * :check f 10 == 20
   * ```
   *
   * Also checked
   * ```
   * :safe f
   * ```
   *
   * Not checked
   * ```cpp
   * int main() {}
   * ```
   */
  f : [8] -> [8]
  f x = 2 * x

Identifiers
-----------

Cryptol identifiers consist of one or more characters.  The first
character must be either an English letter or underscore (``_``).  The
following characters may be an English letter, a decimal digit,
underscore (``_``), or a prime (``'``).  Some identifiers have special
meaning in the language, so they may not be used in programmer-defined
names (see `Keywords and Built-in Operators`_).

.. code-block:: cryptol
  :caption: Examples of identifiers

  name    name1    name'    longer_name
  Name    Name2    Name''   longerName



Keywords and Built-in Operators
-------------------------------

The following identifiers have special meanings in Cryptol, and may
not be used for programmer defined names:

.. The table below can be generated by running `chop.hs` on this list:
  else
  extern
  if
  private
  include
  module
  submodule
  interface
  newtype
  pragma
  property
  then
  type
  where
  let
  import
  as
  hiding
  infixl
  infixr
  infix
  primitive
  parameter
  constraint
  down
  by
.. _Keywords:

.. code-block:: none
  :caption: Keywords

  as              extern      include      interface      parameter      property      where    
  by              hiding      infix        let            pragma         submodule     else      
  constraint      if          infixl       module         primitive      then         
  down            import      infixr       newtype        private        type         

The following table contains Cryptol's operators and their
associativity with lowest precedence operators first, and highest
precedence last.

.. table:: Operator precedences

  +-----------------------------------------+-----------------+
  | Operator                                | Associativity   |
  +=========================================+=================+
  |  ``==>``                                | right           |
  +-----------------------------------------+-----------------+
  |  ``\/``                                 | right           |
  +-----------------------------------------+-----------------+
  |  ``/\``                                 | right           |
  +-----------------------------------------+-----------------+
  |  ``==`` ``!=`` ``===`` ``!==``          | not associative |
  +-----------------------------------------+-----------------+
  |  ``>`` ``<`` ``<=`` ``>=``              | not associative |
  |  ``<$`` ``>$`` ``<=$`` ``>=$``          |                 |
  +-----------------------------------------+-----------------+
  |  ``||``                                 | right           |
  +-----------------------------------------+-----------------+
  |  ``^``                                  | left            |
  +-----------------------------------------+-----------------+
  |  ``&&``                                 | right           |
  +-----------------------------------------+-----------------+
  |  ``#``                                  | right           |
  +-----------------------------------------+-----------------+
  |  ``>>`` ``<<`` ``>>>`` ``<<<`` ``>>$``  | left            |
  +-----------------------------------------+-----------------+
  |  ``+`` ``-``                            | left            |
  +-----------------------------------------+-----------------+
  |  ``*`` ``/`` ``%`` ``/$`` ``%$``        | left            |
  +-----------------------------------------+-----------------+
  |  ``^^``                                 | right           |
  +-----------------------------------------+-----------------+
  |  ``@``  ``@@``  ``!`` ``!!``            | left            |
  +-----------------------------------------+-----------------+
  |  (unary) ``-`` ``~``                    | right           |
  +-----------------------------------------+-----------------+


Built-in Type-level Operators
-----------------------------

Cryptol includes a variety of operators that allow computations on
the numeric types used to specify the sizes of sequences.

.. table:: Type-level operators

  +------------+----------------------------------------+
  | Operator   |   Meaning                              |
  +============+========================================+
  |  ``+``     |  Addition                              |
  +------------+----------------------------------------+
  |  ``-``     |  Subtraction                           |
  +------------+----------------------------------------+
  |  ``*``     |  Multiplication                        |
  +------------+----------------------------------------+
  |  ``/``     |  Division                              |
  +------------+----------------------------------------+
  |  ``/^``    |  Ceiling division (``/`` rounded up)   |
  +------------+----------------------------------------+
  |  ``%``     |  Modulus                               |
  +------------+----------------------------------------+
  |  ``%^``    |  Ceiling modulus (compute padding)     |
  +------------+----------------------------------------+
  |  ``^^``    |  Exponentiation                        |
  +------------+----------------------------------------+
  |  ``lg2``   |  Ceiling logarithm (base 2)            |
  +------------+----------------------------------------+
  |  ``width`` |  Bit width (equal to ``lg2(n+1)``)     |
  +------------+----------------------------------------+
  |  ``max``   |  Maximum                               |
  +------------+----------------------------------------+
  |  ``min``   |  Minimum                               |
  +------------+----------------------------------------+

Numeric Literals
----------------

Numeric literals may be written in binary, octal, decimal, or
hexadecimal notation. The base of a literal is determined by its prefix:
``0b`` for binary, ``0o`` for octal, no special prefix for
decimal, and ``0x`` for hexadecimal.

.. code-block:: cryptol
  :caption: Examples of literals

  254                 // Decimal literal
  0254                // Decimal literal
  0b11111110          // Binary literal
  0o376               // Octal literal
  0xFE                // Hexadecimal literal
  0xfe                // Hexadecimal literal

Numeric literals in binary, octal, or hexadecimal notation result in
bit sequences of a fixed length (i.e., they have type ``[n]`` for
some `n`). The length is determined by the base and the number
of digits in the literal. Decimal literals are overloaded, and so the
type is inferred from context in which the literal is used. Examples:

.. code-block:: cryptol
  :caption: Literals and their types

  0b1010              // : [4],   1 * number of digits
  0o1234              // : [12],  3 * number of digits
  0x1234              // : [16],  4 * number of digits

  10                  // : {a}. (Literal 10 a) => a
                      // a = Integer or [n] where n >= width 10

Numeric literals may also be written as polynomials by writing a polynomial
expression in terms of `x` between an opening ``<|`` and a closing ``|>``.
Numeric literals in polynomial notation result in bit sequences of length
one more than the degree of the polynomial.  Examples:

.. code-block:: cryptol
  :caption: Polynomial literals

  <| x^^6 + x^^4 + x^^2 + x^^1 + 1 |>  // : [7], equal to 0b1010111
  <| x^^4 + x^^3 + x |>                // : [5], equal to 0b11010

Cryptol also supports fractional literals using binary (prefix ``0b``),
octal (prefix ``0o``), decimal (no prefix), and hexadecimal (prefix ``ox``)
digits.  A fractional literal must contain a ``.`` and may optionally
have an exponent.  The base of the exponent for binary, octal,
and hexadecimal literals is 2 and the exponent is marked using the symbol ``p``.
Decimal fractional literals use exponent base 10, and the symbol ``e``.
Examples:

.. code-block:: cryptol
  :caption: Fractional literals

  10.2
  10.2e3            // 10.2 * 10^3
  0x30.1            // 3 * 64 + 1/16
  0x30.1p4          // (3 * 64 + 1/16) * 2^4

All fractional literals are overloaded and may be used with types that support
fractional numbers (e.g., ``Rational``, and the ``Float`` family of types).

Some types (e.g. the ``Float`` family) cannot represent all fractional literals
precisely.  Such literals are rejected statically when using binary, octal,
or hexadecimal notation.  When using decimal notation, the literal is rounded
to the closest representable even number.


All numeric literals may also include ``_``, which has no effect on the
literal value but may be used to improve readability.  Here are some examples:

.. code-block:: cryptol
  :caption: Using _

  0b_0000_0010
  0x_FFFF_FFEA


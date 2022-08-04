Expressions
===========

This section provides an overview of the Cryptol's expression syntax.

Calling Functions
-----------------

.. code-block:: cryptol

  f 2             // call `f` with parameter `2`
  g x y           // call `g` with two parameters: `x` and `y`
  h (x,y)         // call `h` with one parameter,  the pair `(x,y)`


Prefix Operators
-----------------


.. code-block:: cryptol

  -2              // call unary `-` with parameter `2`
  - 2             // call unary `-` with parameter `2`
  f (-2)          // call `f` with one argument: `-2`,  parens are important
  -f 2            // call unary `-` with parameter `f 2`
  - f 2           // call unary `-` with parameter `f 2`


Infix Functions
-----------------


.. code-block:: cryptol

  2 + 3           // call `+` with two parameters: `2` and `3`
  2 + 3 * 5       // call `+` with two parameters: `2` and `3 * 5`
  (+) 2 3         // call `+` with two parameters: `2` and `3`
  f 2 + g 3       // call `+` with two parameters: `f 2` and `g 3`
  - 2 + - 3       // call `+` with two parameters: `-2` and `-3`
  - f 2 + - g 3

Type Annotations
-----------------

Explicit type annotations may be added on expressions, patterns, and
in argument definitions.

.. code-block:: cryptol

  x : Bit         // specify that `x` has type `Bit`
  f x : Bit       // specify that `f x` has type `Bit`
  - f x : [8]     // specify that `- f x` has type `[8]`
  2 + 3 : [8]     // specify that `2 + 3` has type `[8]`
  \x -> x : [8]   // type annotation is on `x`, not the function
  if x
    then y
    else z : Bit  // the type annotation is on `z`, not the whole `if`
  [1..9 : [8]]    // specify that elements in `[1..9]` have type `[8]`

  f (x : [8]) = x + 1   // type annotation on patterns

.. todo::
  Patterns with type variables



Explicit Type Instantiation
----------------------------

If ``f`` is a polymorphic value with type:

.. code-block:: cryptol

  f : { tyParam } tyParam
  f = zero

you can evaluate ``f``, passing it a type parameter:

.. code-block:: cryptol

  f `{ tyParam = 13 }




Local Declarations
------------------

Local declarations have the weakest precedence of all expressions.

.. code-block:: cryptol

  2 + x : [T]
    where
    type T = 8
    x      = 2          // `T` and `x` are in scope of `2 + x : `[T]`

  if x then 1 else 2
    where x = 2         // `x` is in scope in the whole `if`

  \y -> x + y
    where x = 2         // `y` is not in scope in the defintion of `x`


Block Arguments
---------------

When used as the last argument to a function call,
``if`` and lambda expressions do not need parens:

.. code-block:: cryptol

  f \x -> x       // call `f` with one argument `x -> x`
  2 + if x
        then y
        else z    // call `+` with two arguments: `2` and `if ...`


Conditionals
------------

The ``if ... then ... else`` construct can be used with
multiple branches. For example:

.. code-block:: cryptol

  x = if y % 2 == 0 then 22 else 33

  x = if y % 2 == 0 then 1
       | y % 3 == 0 then 2
       | y % 5 == 0 then 3
       else 7


Demoting Numeric Types to Values
--------------------------------

The value corresponding to a numeric type may be accessed using the
following notation:

.. code-block:: cryptol

  `t

Here `t` should be a finite type expression with numeric kind.  The resulting
expression will be of a numeric base type, which is sufficiently large
to accommodate the value of the type:

.. code-block:: cryptol

  `t : {a} (Literal t a) => a

This backtick notation is syntax sugar for an application of the
`number` primtive, so the above may be written as:

.. code-block:: cryptol

  number`{t} : {a} (Literal t a) => a

If a type cannot be inferred from context, a suitable type will be
automatically chosen if possible, usually `Integer`.


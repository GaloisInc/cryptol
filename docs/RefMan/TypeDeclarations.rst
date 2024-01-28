Type Declarations
=================

Type Synonyms
-------------

.. code-block:: cryptol

  type T a b = [a] b

A ``type`` declaration creates a synonym for a
pre-existing type expression, which may optionally have
arguments. A type synonym is transparently unfolded at
use sites and is treated as though the user had instead
written the body of the type synonym in line.
Type synonyms may mention other synonyms, but it is not
allowed to create a recursive collection of type synonyms.

Newtypes
--------

.. code-block:: cryptol

  newtype NewT a b = { seq : [a]b }

A ``newtype`` declaration declares a new named type which is defined by
a record body.  Unlike type synonyms, each named ``newtype`` is treated
as a distinct type by the type checker, even if they have the same
bodies. Moreover, types created by a ``newtype`` declaration will not be
members of any typeclasses, even if the record defining their body
would be.  For the purposes of typechecking, two newtypes are
considered equal only if all their arguments are equal, even if the
arguments do not appear in the body of the newtype, or are otherwise
irrelevant.  Just like type synonyms, newtypes are not allowed to form
recursive groups.

Every ``newtype`` declaration brings into scope a new function with the
same name as the type which can be used to create values of the
newtype.

.. code-block:: cryptol

  x : NewT 3 Integer
  x = NewT { seq = [1,2,3] }

Just as with records, field projections can be used directly on values
of newtypes to extract the values in the body of the type.

.. code-block:: none

  > sum x.seq
  6

Enums
-----

.. code-block:: cryptol

  enum Maybe a = Nothing | Just a

An ``enum`` declaration introduces a new named type, which is defined by a
collection of *constructors*. ``enum`` declarations correspond to the notion of
*algebraic data types*, which are commonly found in other programming
languages. Each named ``enum`` type is treated like a separate type, even if it
has the exact same constructors as another ``enum`` type---in this way ``enum``
is similar to ``newtype`` and unlike ``type`` synonyms.

**Constructors.** The only way to create a value of an ``enum`` type is to
use one of its constructors.   When used in an expression, the constructors
behave like an ordinary function, which has one parameter for each field of the
constructor.  For example, the constructor ``Just`` has a type like this:

.. code-block:: cryptol

   Just: {a} a -> Maybe a

Constructors may have 0 or multiple fields, and values created with different
constructors are always distinct.

**Case Expressions.** The only way to examine a value of an ``enum`` type is
with a ``case`` expression, which are similar to ``if`` expressions:

.. code-block:: cryptol

  case e of
    Nothing -> 0
    Just a  -> a + 1

In this example, ``e`` is an expression of type ``Maybe``:

  * if it was created with the ``Nothing`` constructor,
    then we'll use the first branch of the ``case`` expression and
    result of the whole expression would be 0;

  * if, ``e`` was create by applying the ``Just`` constructor to some
    value (e.g, ``Just 2``), then we'll use the second branch of the ``case``
    expression, and the variable ``a`` will be bound to the value of the field
    (e.g., ``2``), and the whole expression will evaluate to ``a + 1``
    (e.g., ``3``).

It is also possible to use just a variable (or ``_``) in a case expression
to define a catch-all clause---if a value does not match any of the previous
cases, then this branch will be used:

.. code-block:: cryptol

  isNothing x =
    case x of
      Nothing -> True
      _       -> False

**Upper Case Restriction.**
The names of the constructors in an ``enum`` declarations
need to start with an upper-case letter.  This restriction makes it possible
to distinguish between constructors and variable
bindings in ``case`` patterns (e.g., between ``Just`` and ``a`` in the
previous example).

**Non Recursive.** The fields in a constructor may be of any value type,
as long as this type does not depend on the type to which the constructor
belongs.  This means that we do not support defining recursive types,
such as linked lists.

**No Nested Constructor Patterns.**  For simplicity, only non-constructor
patterns may be used in the fields of a constructor pattern.  For example,
``Just (a,b)`` and ``Just (a # b)`` are OK, however, ``Just (Just a)``
will be rejected.  This is a restriction that we may lift in the future.

**No Overlapping Patterns.** For simplicity, all patterns in a
``case`` expression must be disjoint. In particular, this means that:

  * No two patterns in a ``case`` expression can match the same constructor.
    This means that Cryptol will reject the following example:

    .. code-block:: cryptol

      isNothing x =
        case x of
          Nothing -> True
          Nothing -> False

  * If a ``case`` expression uses a catch-all clause, then that clause must
    occur last in the expression. It is an error to match on additional
    patterns after the catch-all clause. For instance, Cryptol will reject the
    following example:

    .. code-block:: cryptol

      isNothing x =
        case x of
          Just _  -> False
          _       -> True
          Nothing -> False

**Patterns Must Be Exhaustive.** The patterns in a ``case`` expression must
cover all constructors in the ``enum`` type being matched on. For example,
Cryptol will reject the following example, as it does not cover the ``Just``
constructor:

.. code-block:: cryptol

  isNothing x =
    case x of
      Nothing -> True

**The Matched Expression Must Have an Unambiguous Type.** Cryptol will reject
the definition of ``f``, where ``f`` lacks a type signature:

.. code-block:: cryptol

  f x =
    case x of
      _ -> ()

This is because it is not clear what the type of ``x`` (the expression being
matched) should be. The only pattern is a catch-all case, which does not reveal
anything about the type of ``x``. It would be incorrect to give ``f`` this type:

.. code-block:: cryptol

  f : {a} a -> ()

This is because ``f`` is not really polymorphic in its argument type, as the
only values that can be matched in a ``case`` expression are those whose type
was declared as an ``enum``. As such, Cryptol rejects this example.

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


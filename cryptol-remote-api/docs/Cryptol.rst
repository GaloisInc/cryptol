==================
Cryptol Evaluation
==================

All methods in this section additionally propagate server state in the
manner described in the prior section.

These methods may return :ref:`a variety of Cryptol errors
<cryptol-server-errors>`, with codes in the range of ``20000``-``29999``.

Module Management
=================

Changing Directories
--------------------

:Method name:
  ``change directory``
:Parameters:
  - ``directory``: The new working directory, represented as a string.

Loading Modules
---------------

:Method name:
  ``load module``
:Parameters:
  - ``module name``: The name of the Cryptol module to be loaded.

Loading Files
-------------

:Method name:
  ``load file``
:Parameters:
  - ``file``: The name of the Cryptol source file to be loaded.

Module Context
--------------

:Method name:
  ``focused module``
:Parameters: none
:Return fields:
  - ``module``: The name of the focused module, which would be shown in the
    prompt in the Cryptol REPL, or ``null`` if there is no such focused module.
  - ``parameterized``: A Boolean value indicating whether the focused module is
    parameterized. This field is only present when the module name is not
    ``null``.

Evaluation and Typechecking
===========================

Evaluating Expressions
----------------------

This method evaluates a Cryptol expression. The type of the expression
needs to be fully-determined and finite - that is, functions and
infinite streams are not supported, and neither is polymorphism.

:Method name:
  ``evaluate expression``
:Parameters:
  - ``expression``: The :ref:`JSON Cryptol expression <cryptol-json-expression>` to be evaluated
:Return fields:
  - ``value``: A :ref:`JSON Cryptol expression <cryptol-json-expression>` that denotes the value
  - ``type``: A :ref:`JSON Cryptol type <cryptol-json-type>` that denotes the result type
  - ``type string``: A human-readable representation of the result type

Calling Functions
-----------------

Note: this method may be removed in the future, because its abilities
have been subsumed by ``evaluate expression``.

This method applies a Cryptol function to some arguments. The type of
the resulting expression needs to be fully-determined and finite -
that is, functions and infinite streams are not supported, and neither
is polymorphism.

:Method name:
  ``call``
:Parameters:
  - ``function``: The name of a Cryptol function that is currently in scope
  - ``arguments``: A list of arguments to the function, encoded as JSON
    Cryptol expressions
:Return fields:
  - ``value``: A :ref:`JSON Cryptol expression <cryptol-json-expression>` that denotes the value
  - ``type``: A :ref:`JSON Cryptol type <cryptol-json-type>` that denotes the result type
  - ``type string``: A human-readable representation of the result type

Visible Names
-------------

Return information about all names in scope.

:Method name:
  ``visible names``
:Parameters: none
:Return value:
  A list of name information objects. Each name information object has the following
  fields:

  - ``name``: A human-readable representation of the name
  - ``type string``: A human-readable representation of the name's type schema
  - ``type``: A :ref:`JSON Cryptol type <cryptol-json-type>`

  Some will additionally have the following field:

  - ``documentation``: The documentation string for the name, if it is documented

Checking Types
--------------

Check the type of an expression.

:Method name:
  ``check type``
:Parameters:
  - ``expression``: A :ref:`JSON Cryptol expression <cryptol-json-expression>` for which a type is desired.
:Return fields:
  - ``type schema``: A :ref:`JSON Cryptol type <cryptol-json-type>`

SAT
---

This method is not yet ready for public consumption.

Terms and Types
===============

.. _cryptol-json-expression:

JSON Cryptol Expressions
------------------------

In the API, Cryptol expressions can be represented by the following:

JSON Booleans
  Represent the corresponding Cryptol Booleans

JSON Integers
  Cryptol integer literals, that can be used at a variety of types

JSON Strings
  Cryptol concrete syntax

JSON Objects
  Objects can represent a variety of Cryptol expressions. The field
  ``expression`` contains a tag that can be used to determine the
  remaining fields.

The tag values in objects can be:

``bits``
  The expression is a bitvector. Further fields are:

  + ``encoding``: Either the string ``base64`` or ``hex``, for base-64 or hexadecimal
    representations of the bitvector
  + ``data``: A string containing the actual data
  + ``width``: An integer: the bit-width of the represented bit vector

``record``
  The expression is a record. The field ``data`` is a JSON
  object that maps record field names to :ref:`JSON Cryptol expressions <cryptol-json-expression>`.

``sequence``
  The expression is a sequence. The field ``data`` contains a
  JSON array of the elements of the sequence; each is a JSON Cryptol
  expression.

``tuple``
  The expression is a tuple. The field ``data`` contains a JSON
  array of the elements of the tuple; each is a JSON Cryptol
  expression.

``unit``
  The expression is the unit constructor, and there are no further fields.

``let``
  The expression is a ``where`` binding. The fields are:

  ``binders``
    A list of binders. Each binder is an object with two fields:

    - ``name``: A string that is the name to be bound, and
    - ``definition``: A :ref:`JSON Cryptol expression <cryptol-json-expression>`.

  ``body``
    A :ref:`JSON Cryptol expression <cryptol-json-expression>` in which the bound names may be used.

``call``
  The expression is a function application. Further fields are:

  - ``function``: A :ref:`JSON Cryptol expressions <cryptol-json-expression>`.
  - ``arguments``: A JSON array of :ref:`JSON Cryptol expressions <cryptol-json-expression>`.

``instantiate``
  The expression is a type application. Further fields are:

  - ``generic``: The polymorphic expression to be instantiated
  - ``arguments``: A JSON object in which keys are the names of type parameters and values are :ref:`JSON Cryptol types <cryptol-json-type>`.

``integer modulo``
  The expression is an integer with a modulus (the Cryptol ``Z`` type). Further fields are:

  - ``integer``: A JSON number, representing the integer
  - ``modulus``: A JSON number, representing the modulus

.. _cryptol-json-type:

JSON Cryptol Types
------------------

JSON representations of types are type schemas. A type schema has
three fields:

``forall``

  Contains an array of objects. Each object has two fields: ``name``
  is the name of a type variable, and ``kind`` is its kind. There
  are four kind formers: the string ``Type`` represents ordinary
  datatypes, the string ``Num`` is the kind of numbers, and
  ``Prop`` is the kind of propositions. Arrow kinds are represented
  by objects in which the field ``kind`` is the string ``arrow``,
  and the fields ``from`` and ``to`` are the kinds on the left and
  right side of the arrow, respectively.

``propositions``
  A JSON array of the constraints in the type.

``type``
  The type in which the variables from ``forall`` are in scope and
  the constraints in ``propositions`` are in effect.

Concrete Types
~~~~~~~~~~~~~~

Types are represented as JSON objects. The ``type`` field contains one of the following tags (represented as JSON strings):

``variable``
  The type is a type variable. The remaining fields are ``name``,
  which contains the variable's name, and ``kind``, which contains
  its kind (represented as in the ``forall`` section). When providing
  types to Cryptol, the ``kind`` field should be elided, and type synonyms
  may be provided with arguments through an optional ``arguments`` field.

``record``
  The type is a record type. The remaining field is ``fields``,
  which contains a JSON object whose keys are the names of fields and
  whose values are the fields' types.

``number``
  The type is a number. The field ``value`` contains the number
  itself.

``inf``
  The type is the infinite number. There are no further fields.

``Bit``
  The type is the bit type. There are no further fields.

``Integer``
  The type is the integer type. There are no further fields.

``Rational``
  The type is the rational number type. There are no further fields.

``Z``
  The type is integers modulo another value. The field ``modulus``
  contains the modulus, which is a type.

``bitvector``
  The type is a bitvector. The field ``width`` contains the number
  of bits, which is a type.

``sequence``
  The type is a sequence. The field ``length`` contains the length
  of the sequence (a type), and the field ``contents`` contains the
  type of entries in the sequence.

``function``
  The type is a function type. The fields ``domain`` and ``range``
  contain the domain and range types.

``unit``
  The type is the unit type. There are no further fields.

``tuple``
  The type is a tuple. The field ``contents`` is a JSON array
  containing the types of the projections from the tuple.

One of ``+``, ``-``, ``*``, ``/``, ``%``, ``^^``, ``width``, ``min``, ``max``, ``/^``, ``%^``, ``lengthFromThenTo``
  The type is an application of the indicated type function. The
  arguments are contained in the ``arguments`` field, as a JSON
  array.

Propositions
~~~~~~~~~~~~

Propositions/constraints have the key ``prop``, mapped to one of the
following tags:

``==``
  Equality. The equated terms are in the ``left`` and ``right``
  fields.

``!=``
  Inequality. The disequated terms are in the ``left`` and
  ``right`` fields.

``>=``
  Greater than. The greater type is in the ``greater`` field and the
  lesser type is in the ``lesser`` field.

``fin``
  Finitude. The finite type is in the ``subject`` field.

``has``
  The selector is in the ``selector`` field, the type that has this
  selector is in the ``type`` field, and the type expected for the
  projection is in the ``is`` field.

``Arith``, ``Cmp``, ``SignedCmp``, ``Zero``, ``Logic``
  The type that has these operations defined is in the ``subject``
  field.

``Literal``
  The size is in the ``size`` field, and the type is in the
  ``subject`` field.

``True``
  There are no further fields.

``And``
  The conjuncts are in the ``left`` and ``right`` fields.

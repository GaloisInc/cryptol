Overloaded Operations
=====================

Many built-in Cryptol operations are *overloaded*, which means that the same
function can be used with many different types. The types that an overloaded
operation can be used with are defined by *constraints*, and a type that
satisfies a constraint is said to be an *instance* of that constraint.

Cryptol has a number of :ref:`built-in instances <built-in-instances>`, and you
can also :ref:`derive instances <derived-instances>` for :ref:`user-defined
types <type-declarations>`.

.. _built-in-instances:

Built-in instances
------------------

Equality
~~~~~~~~

.. code-block:: cryptol

  Eq
    (==)        : {a}    (Eq a) => a -> a -> Bit
    (!=)        : {a}    (Eq a) => a -> a -> Bit
    (===)       : {a, b} (Eq b) => (a -> b) -> (a -> b) -> (a -> Bit)
    (!==)       : {a, b} (Eq b) => (a -> b) -> (a -> b) -> (a -> Bit)


.. list-table:: Instances

  * - Type
    - Condition
  * - ``Bit``
    -
  * - ``Integer``
    -
  * - ``Rational``
    -
  * - ``Z n``
    - ``fin n``, ``n >= 1``
  * - ``Float e p``
    - ``ValidFloat e p``
  * - ``[n] a``
    - ``fin n``, ``Eq a``
  * - ``(a,b)``
    - ``Eq a``, ``Eq b``
  * - ``{f1 : a, f2 : b}``
    - ``Eq a``, ``Eq b``
  * - ``Option a``
    - ``Eq a``
  * - ``Result t e``
    - ``Eq t``, ``Eq e``



Comparisons
~~~~~~~~~~~

.. code-block:: cryptol

  Cmp
    (<)         : {a} (Cmp a) => a -> a -> Bit
    (>)         : {a} (Cmp a) => a -> a -> Bit
    (<=)        : {a} (Cmp a) => a -> a -> Bit
    (>=)        : {a} (Cmp a) => a -> a -> Bit
    min         : {a} (Cmp a) => a -> a -> a
    max         : {a} (Cmp a) => a -> a -> a
    abs         : {a} (Cmp a, Ring a) => a -> a


.. list-table:: Instances

  * - Type
    - Condition
  * - ``Bit``
    -
  * - ``Integer``
    -
  * - ``Rational``
    -
  * - ``Float e p``
    - ``ValidFloat e p``
  * - ``[n] a``
    - ``fin n``, ``Cmp a``
  * - ``(a,b)``
    - ``Cmp a``, ``Cmp b``
  * - ``{f1 : a, f2 : b}``
    - ``Cmp a``, ``Cmp b``
  * - ``Option a``
    - ``Cmp a``
  * - ``Result t e``
    - ``Cmp t``, ``Cmp e``





Signed Comparisons
~~~~~~~~~~~~~~~~~~

.. code-block:: cryptol

  SignedCmp
    (<$)        : {a} (SignedCmp a) => a -> a -> Bit
    (>$)        : {a} (SignedCmp a) => a -> a -> Bit
    (<=$)       : {a} (SignedCmp a) => a -> a -> Bit
    (>=$)       : {a} (SignedCmp a) => a -> a -> Bit

.. list-table:: Instances

  * - Type
    - Condition
  * - ``[n] Bit``
    - ``fin n``, ``n >= 1``
  * - ``[n] a``
    - ``fin n``, ``SignedCmp a``, ``a /= Bit``
  * - ``(a,b)``
    - ``SignedCmp a``, ``SignedCmp b``
  * - ``{f1 : a, f2 : b}``
    - ``SignedCmp a``, ``SignedCmp b``
  * - ``Option a``
    - ``SignedCmp a``
  * - ``Result t e``
    - ``SignedCmp t``, ``SignedCmp e``


Zero
~~~~

.. code-block:: cryptol

  Zero
    zero        : {a} (Zero a) => a

.. list-table:: Instances

  * - Type
    - Condition
  * - ``Bit``
    -
  * - ``Integer``
    -
  * - ``Rational``
    -
  * - ``Z n``
    - ``fin n``, ``n >= 1``
  * - ``Float e p``
    - ``ValidFloat e p``
  * - ``[n] a``
    - ``Zero a``
  * - ``a -> b``
    - ``Zero b``
  * - ``(a,b)``
    - ``Zero a``, ``Zero b``
  * - ``{f1 : a, f2 : b}``
    - ``Zero a``, ``Zero b``

Logical Operations
~~~~~~~~~~~~~~~~~~

.. code-block:: cryptol

  Logic
    (&&)        : {a} (Logic a) => a -> a -> a
    (||)        : {a} (Logic a) => a -> a -> a
    (^)         : {a} (Logic a) => a -> a -> a
    complement  : {a} (Logic a) => a -> a

.. list-table:: Instances

  * - Type
    - Condition
  * - ``Bit``
    -
  * - ``[n] a``
    - ``Logic a``
  * - ``a -> b``
    - ``Logic b``
  * - ``(a,b)``
    - ``Logic a``, ``Logic b``
  * - ``{f1 : a, f2 : b}``
    - ``Logic a``, ``Logic b``



Basic Arithmetic
~~~~~~~~~~~~~~~~

.. code-block:: cryptol

  Ring
    fromInteger : {a} (Ring a) => Integer -> a
    (+)         : {a} (Ring a) => a -> a -> a
    (-)         : {a} (Ring a) => a -> a -> a
    (*)         : {a} (Ring a) => a -> a -> a
    negate      : {a} (Ring a) => a -> a
    (^^)        : {a, e} (Ring a, Integral e) => a -> e -> a

.. list-table:: Instances

  * - Type
    - Condition
  * - ``Integer``
    -
  * - ``Rational``
    -
  * - ``Z n``
    - ``fin n``, ``n >= 1``
  * - ``Float e p``
    - ``ValidFloat e p``
  * - ``[n] Bit``
    - ``fin n``
  * - ``[n] a``
    - ``Ring a``, ``a /=  Bit``
  * - ``a -> b``
    - ``Ring b``
  * - ``(a,b)``
    - ``Ring a``, ``Ring b``
  * - ``{f1 : a, f2 : b}``
    - ``Ring a``, ``Ring b``



Integral Operations
~~~~~~~~~~~~~~~~~~~

.. code-block:: cryptol

  Integral
    (/)         : {a} (Integral a) => a -> a -> a
    (%)         : {a} (Integral a) => a -> a -> a
    (^^)        : {a, e} (Ring a, Integral e) => a -> e -> a
    toInteger   : {a} (Integral a) => a -> Integer
    infFrom     : {a} (Integral a) => a -> [inf]a
    infFromThen : {a} (Integral a) => a -> a -> [inf]a

.. list-table:: Instances

  * - Type
    - Condition
  * - ``Integer``
    -
  * - ``[n] Bit``
    - ``fin n``





Division
~~~~~~~~

.. code-block:: cryptol

  Field
    recip       : {a} (Field a) => a -> a
    (/.)        : {a} (Field a) => a -> a -> a


.. list-table:: Instances

  * - Type
    - Condition
  * - ``Rational``
    -
  * - ``Z n``
    - ``prime n``
  * - ``Float e p``
    - ``ValidFloat e p``



Rounding
~~~~~~~~

.. code-block:: cryptol

  Round
    ceiling     : {a} (Round a) => a -> Integer
    floor       : {a} (Round a) => a -> Integer
    trunc       : {a} (Round a) => a -> Integer
    roundAway   : {a} (Round a) => a -> Integer
    roundToEven : {a} (Round a) => a -> Integer


.. list-table:: Instances

  * - Type
    - Condition
  * - ``Float e p``
    - ``ValidFloat e p``


.. _derived-instances:

Derived instances
-----------------

A :ref:`newtype <newtypes>` or :ref:`enum <enums>` declaration can optionally
have a ``deriving`` clause attached to it to *derive* instances of the type for
certain constraints. Like built-in instances, the derived instances may have
certain conditions that need to be satisifed for them to be valid.

Newtypes
~~~~~~~~

The following constraints can be derived for newtypes:

  * ``Eq``
  * ``Cmp``
  * ``SignedCmp``
  * ``Zero``
  * ``Logic``
  * ``Ring``

The condition for a newtype to be an instance of any of the above constraints is
that the underlying record type of the newtype is also an instance of that
constraint. For instance, if you have

.. code-block:: cryptol

  newtype T a b = { f1 : a, f2 : b } deriving (Eq, Cmp)

then ``Eq (T a b)`` will only hold if ``Eq ({f1 : a, f2 : b})`` holds, which in
turn will only hold if both ``Eq a`` and ``Eq b`` hold. Similarly, ``Cmp (T a
b)`` will only hold if ``Cmp ({f1 : a, f2 : b})`` holds, which in turn will only
hold if both ``Cmp a`` and ``Cmp b`` hold.

The behavior of the built-in overloaded operations on newtypes with derived
instances is exactly the same as the behavior on their underlying record types,
modulo the appropriate wrapping and unwrapping of the newtype constructor.

Enums
~~~~~

The following constraints can be derived for enums:

  * ``Eq``
  * ``Cmp``
  * ``SignedCmp``

The condition for an enum to be an instance of any of the above constraints is
that all the fields of all its constructors are instances of that constraint.
For instance, if you have

.. code-block:: cryptol

  enum T a b = A a | B b deriving (Eq, Cmp)

then ``Eq (T a b)`` will only hold if ``Eq a`` and ``Eq b`` hold, and ``Cmp (T a
b)`` will only hold if ``Cmp a`` and ``Cmp b`` hold.

Two enum values of the same type compare equal if they have the same constructor
and the same field values for that constructor, and unequal otherwise. For
instance, using the ``T`` type above, ``A 0x0 == A 0x0``, but ``A 0x0 != A 0x1``
and ``A 0x0 != B 0x0``.

Two enum values of the same type are ordered first by their constructor, then
for values with the same constructor, by lexicographic ordering on the fields of
that constructor. The order of constructors is the order in which they are
listed in the ``enum`` declaration; constructors listed earlier compare less
than constructors listed later. In the above example of ``T a b``, any value
with constructor ``A`` always compares less than any value with constructor
``B``. So you would have ``A 0x0 < A 0x1 < B 0x0 < B 0x1``. For signed
comparisons, fields are compared using signed comparisons but constructors
themselves are still ordered in the same way, so ``A (-1) <$ A 1 <$ B
(-1) <$ B 1``.

The ``Eq``, ``Cmp``, and ``SignedCmp`` instances for the built-in ``Option`` and
``Result`` types are actually just standard derived instances, so they work the
same way as described above (for instance, ``None < Some x``, ``Ok x < Err
y``).

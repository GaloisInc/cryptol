Overloaded Operations
=====================

Equality
--------

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



Comparisons
-----------

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





Signed Comparisons
------------------

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


Zero
----

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

Logical Operations
------------------

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



Basic Arithmetic
----------------

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



Integral Operations
-------------------

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
--------

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
--------

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



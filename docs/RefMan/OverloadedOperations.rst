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


Signed Comparisons
------------------

.. code-block:: cryptol

  SignedCmp
    (<$)        : {a} (SignedCmp a) => a -> a -> Bit
    (>$)        : {a} (SignedCmp a) => a -> a -> Bit
    (<=$)       : {a} (SignedCmp a) => a -> a -> Bit
    (>=$)       : {a} (SignedCmp a) => a -> a -> Bit


Zero
----

.. code-block:: cryptol

  Zero
    zero        : {a} (Zero a) => a

Logical Operations
------------------

.. code-block:: cryptol

  Logic
    (&&)        : {a} (Logic a) => a -> a -> a
    (||)        : {a} (Logic a) => a -> a -> a
    (^)         : {a} (Logic a) => a -> a -> a
    complement  : {a} (Logic a) => a -> a

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


Division
--------

.. code-block:: cryptol

  Field
    recip       : {a} (Field a) => a -> a
    (/.)        : {a} (Field a) => a -> a -> a

Rounding
--------

.. code-block:: cryptol

  Round
    ceiling     : {a} (Round a) => a -> Integer
    floor       : {a} (Round a) => a -> Integer
    trunc       : {a} (Round a) => a -> Integer
    roundAway   : {a} (Round a) => a -> Integer
    roundToEven : {a} (Round a) => a -> Integer

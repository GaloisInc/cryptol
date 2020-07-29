# 2.9.0

## Language changes

* Removed the `Arith` class. Replaced it instead with more specialized
  numeric classes: `Ring`, `Integral`, `Field`, and `Round`.  `Ring`
  is the closest analogue to the old `Arith` class; it contains the
  `fromInteger`, `(+)`, `(*)`, `(-)` and `negate` methods.  `Ring`
  contains all the base arithmetic types in Cryptol, and lifts
  pointwise over tuples, sequences and functions, just as `Arith` did.

  The new `Integral` class now contains the integer division and
  modulus methods (`(/)` and `(%)`), and the sequence indexing,
  sequence update and shifting operations are generalized over
  `Integral`.  The `toInteger` operation is also generalized over this
  class.  `Integral` contains the bitvector types and `Integer`.

  The new `Field` class contains types representing mathematical
  fields (or types that are approximately fields). It is currently
  inhabited by the new `Rational` type, and the `Float`
  family of types.  It will eventually also contain the
  `Real` type. It has the operation `recip` for reciprocal
  and `(/.)` for field division (not to be confused for `(/)`,
  which is Euclidean integral division).

  There is also a new `Round` class for types that can sensibly be
  rounded to integers.  This class has the methods `floor`, `ceiling`,
  `trunc`, `roundToEven` and `roundAway` for performing different
  kinds of integer rounding.  `Rational` and `Float` inhabit `Round`.

  The type of `(^^)` is modified to be
  `{a, e} (Ring a, Integral e) => a -> e -> a`. This makes it clear
  that the semantics are iterated multiplication, which makes sense
  in any ring.

  Finally, the `lg2`, `(/$)` and `(%$)` methods of `Arith` have
  had their types specialized so they operate only on bitvectors.

* Added an `Eq` class, and moved the equality operations
  from `Cmp` into `Eq`. The `Z` type becomes a member of `Eq`
  but not `Cmp`.

* Added a base `Rational` type.  It is implemented as a pair of
  integers, quotiented in the usual way.  As such, it reduces to the
  theory of integers and requires no new solver support (beyond
  nonlinear integer arithmetic).  `Rational` inhabits the new
  `Field` and `Round` classes.  Rational values can be
  constructed using the `ratio` function, or via `fromInteger`.

* The `generate` function (and thus `x @ i= e` definitions) has had
  its type specialized so the index type is always `Integer`.

* The new typeclasses are arranged into a class hierarchy, and the
  typechecker will use that information to infer superclass instances
  from subclasses.

* Added a family of base types, `Float e p`, for working with
  floating point numbers.  The parameters control the precision of
  the numbers, with `e` being the number of bits to use in the exponent
  and `p-1` being the number of bits to use in the mantissa.
  The `Float` family of types may be used through the usual overloaded
  functionality in Cryptol, and there is a new built-in module called
  `Float`, which contains functionality specific to floating point numbers.

* Add a way to write fractional literals in base 2,8,10, and 16.
  Fractional literals are overloaded, and may be used for different types
  (currently `Rational` and the `Float` family).  Fractional literal in base
  2,8,and 16 must be precise, and will be rejected statically if they cannot be
  represented exactly.  Fractional literals in base 10 are rounded to the
  nearest even representable number.

* Changes to the defaulting algorithm. The new algorithm only applies
  to constraints arising from literals (i.e., `Literal` and `FLiteral`
  constraints).  The guiding principle is that we now default these
  to one of the infinite precision types `Integer` or `Rational`.
  `Literal` constraints are defaulted to `Integer`, unless the corresponding
  type also has `Field` constraint, in which case we use `Rational`.
  Fractional literal constraints are always defaulted to `Rational.


## New features

* Document the behavior of lifted selectors.

* Added support for symbolic simulation via the `What4` library
  in addition to the previous method based on `SBV`. The What4
  symbolic simulator is used when selecting solvers with the `w4`
  prefix, such as `w4-z3`, `w4-cvc4`, `w4-yices`, etc.
  The `SBV` and `What4` libraries make different tradeoffs in how
  they represent formulae. You may find one works better than another
  for the same problem, even with the same solver.

* More detailed information about the status of various symbols
  in the output of the `:browse` command (issue #688).

* The `:safe` command will attempt to prove that a given Cryptol
  term is safe; in other words, that it will not encounter a run-time
  error for all inputs. Run-time errors arise from things like
  division-by-zero, index-out-of-bounds situations and
  explicit calls to `error` or `assert`.

* The `:prove` and `:sat` commands now incorporate safety predicates
  by default. In a `:sat` call, models will only be found that do not
  cause run-time errors. For `:prove` calls, the safety conditions are
  added as additional proof goals.  The prior behavior
  (which ignored safety conditions) can be restored using
  `:set ignore-safety = on`.

* Improvements to the `any` prover. It will now shut down external
  prover processes correctly when one finds a solution. It will also
  wait for the first _successful_ result to be returned from a prover,
  instead of failing as soon as one prover fails.

* An experimental `parmap` primitive that applies a function to a
  sequence of arguments and computes the results in parallel.  This
  operation should be considered experimental and may significantly
  change or disappear in the future, and could possibly uncover
  unknown race conditions in the interpreter.

## Bug fixes

* Closed issues #346, #444, #614, #617, #636, #660, #662, #663, #664, #667, #670,
  #702, #711, #712, #716, #723, #725, #731

# 2.8.0 (September 4, 2019)

## New features

* Added support for indexing on the left-hand sides of declarations,
  record field constructors, and record updaters (issue #577). This
  builds on a new primitive function called `generate`, where the new
  syntax `x @ i = e` is sugar for `x = generate (\i -> e)`.

* Added support for element type ascriptions on sequence enumerations.
  The syntax `[a,b..c:t]` indicates that the elements should be of type
  `t`.

* Added support for wildcards in sequence enumerations. For example, the
  syntax `[1 .. _] : [3][8]` yields `[0x01, 0x02, 0x03]`. It can also be
  used polymorphically. For example, the most general type of `[1 .. _]`
  is `{n, a} (n >= 1, Literal n a, fin n) => [n]a`

* Changed the syntax of type signatures to allow multiple constraint
  arrows in type schemas (issue #599). The following are now equivalent:

        f : {a} (fin a, a >= 1) => [a] -> [a]

        f : {a} (fin a) => (a >= 1) => [a] -> [a]

* Added a mechanism for user-defined type constraint operators, and use
  this to define the new type constraint synonyms (<) and (>) (issues
  #400, #618).

* Added support for primitive type declarations. The prelude now uses
  this mechanism to declare all of the basic types.

* Added support for Haskell-style "block arguments", reducing the need
  for parentheses in some cases. For example, `generate (\i -> i +1)`
  can now be written `generate \i -> i + 1`.

* Improved shadowing errors (part of the fix for issue #569).

## Bug fixes

* Closed many issues, including #265, #367, #437, #508, #522, #549,
  #557, #559, #569, #578, #590, #595, #596, #601, #607, #608, #610,
  #615, #621, and #636.

# 2.7.0 (April 30, 2019)

## New features

* Added syntax for record updates (see #399 for details of implemented
and planned features).

* Updated the `:browse` command to list module parameters (issue #586).

* Added support for test vector creation (the `:dumptests` command).
This feature computes a list of random inputs and outputs for the
given expression of function type and saves it to a file. This is
useful for generating tests from a trusted Cryptol specification to
apply to an implementation written in another language.

## Breaking changes

* Removed the `[x..]` construct from the language (issue #574). It
was shorthand for `[x..2^^n-1]` for a bit vector of size `n`, which was
often not what the user intended. Users should instead write either
`[x..y]` or `[x...]`, to construct a smaller range or a lazy sequence,
respectively.

* Renamed the value-level `width` function to `length`, and generalized
its type (issue #550). It does not behave identically to the
type-level `width` operator, which led to confusion. The name
`length` matches more closely with similar functions in other
languages.

## Bug fixes

* Improved type checking performance of decimal literals.

* Improved type checking of `/^` and `%^` (issues #581, #582).

* Improved performance of sequence updates with the `update` primitive
(issue #579).

* Fixed elapsed time printed by `:prove` and `:sat` (issue #572).

* Fixed SMT-Lib formulas generated for right shifts (issue #566).

* Fixed crash when importing non-parameterized modules with the
backtick prefix (issue #565).

* Improved performance of symbolic execution for `Z n` (issue #554).

* Fixed interpretation of the `satNum` option so finding multiple
solutions doesn't run forever (issue #553).

* Improved type checking of the `length` function (issue #548).

* Improved error message when trying to prove properties in
parameterized modules (issue #545).

* Stopped warning about defaulting at the REPL when `warnDefaulting` is
set to `false` (issue #543).

* Fixed builds on non-x86 architectures (issue #542).

* Made browsing of interactively-bound identifiers work better (issue #538).

* Fixed a bug that allowed changing the semantics of the `_ # _`
pattern and the `-` and `~` operators by creating local definitions
of functions that they expand to (issue #568).

* Closed issues #498, #547, #551, #562, and #563.

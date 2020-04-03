# NEXT 

## New features

* Added support for symbolic simulation via the `What4` library
  in addition to the previous method based on `SBV`. The What4
  symbolic simulator is used when selecting solvers with the `w4`
  prefix, such as `w4-z3`, `w4-cvc4`, `w4-yices`, etc.

* More detailed information about the status of various symbols
  in the output of the `:browse` command (issue #688).

## Bug fixes

* Closed issues #346, #444, #614, #617, #660, #662, #663, #664, #667, #670

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

## Solver versions

Cryptol can interact with a variety of external SMT solvers to
support the `:prove` and `:sat` commands, and requires Z3 for its
type checker. Many versions of these solvers will work correctly, but
for Yices and Z3 we recommend the following specific versions.

* Z3 4.7.1
* Yices 2.6.1

For Yices, this is the latest version at the time of this writing.
For Z3, it is not, and the latest versions (4.8.x) include changes
that cause some examples that previously succeeded to time out when
type checking.

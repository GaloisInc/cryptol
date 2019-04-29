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

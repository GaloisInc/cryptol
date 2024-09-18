# next -- TBA

## Language changes

## Bug fixes

* Fix #1740, removes duplicated width from word values.
  Note that since this changes the types, it may require changes to libraries
  depending on Cryptol.

* Fix a bug in which splitting a `[0]` value into type `[inf][0]` would panic.
  ([#1749](https://github.com/GaloisInc/cryptol/issues/1749))

## New features

# 3.2.0 -- 2024-08-20

## Language changes

* Add implicit imports for non-anonymous modules defined by functor
  instantiation.   For details, see #1691.

## Bug fixes

* Fix #1685, which caused Cryptol to panic when given a local definition without
  a type signature that uses numeric constraint guards.

* Fix #1593 and #1693, two related bugs that would cause Cryptol to panic when
  checking ill-typed constraint guards for exhaustivity.

* Fix #1675, which could cause `PrimeEC` to produce incorrect results.

* Fix #1489, which allows for the type checker to reason about exponents.

## New features

* New REPL command :focus enables specifying a submodule scope for evaluating
  expressions.

  ```repl
  :focus submodule M
  :browse
  ```

* New REPL command :check-docstrings extracts code-blocks from docstring
  comments from a module. Code blocks can be delimited with three-or-more
  backticks using the language "repl". Code blocks are evaluated in a local
  REPL context and checked to pass.

  ````cryptol
  /**
   * ```repl
   * :exhaust f
   * ```
   */
  f : [8] -> Bool
  f x = x + 1 - 1 == x
  ````

# 3.1.0 -- 2024-02-05

## Language changes

* Cryptol now supports *enum* declarations. An enum is a named typed which is
  defined by one or more constructors. Enums correspond to the notion of
  algebraic data types, which are commonly found in other programming
  languages.  See the [manual
  section](https://galoisinc.github.io/cryptol/master/TypeDeclarations.html#enums)
  for more information.

* Add two enum declarations to the Cryptol standard library:

  ```
  enum Option a = None | Some a

  enum Result t e = Ok t | Err e
  ```

  These types are useful for representing optional values (`Option`) or values
  that may fail in some way (`Result`).

* `foreign` functions can now have an optional Cryptol implementation, which by
  default is used when the foreign implementation cannot be found, or if the FFI
  is unavailable. The `:set evalForeign` REPL option controls this behavior.

## Bug fixes

* Fixed #1455, making anything in scope of the functor in scope at the REPL as
  well when an instantiation of the functor is loaded and focused, design
  choice (3) on the ticket.  In particular, the prelude will be in scope.

* Fix #1578, which caused `parmap` to crash when evaluated on certain types of
  sequences.

* Closed issues #813, #1237, #1397, #1446, #1486, #1492, #1495, #1537,
  #1538, #1542, #1544, #1548, #1551, #1552, #1554, #1556, #1561, #1562, #1566,
  #1567, #1569, #1571, #1584, #1588, #1590, #1598, #1599, #1604, #1605, #1606,
  #1607, #1609, #1610, #1611, #1612, #1613, #1615, #1616, #1617, #1618, and
  #1619.

* Merged pull requests #1429, #1512, #1534, #1535, #1536, #1540, #1541, #1543,
  #1547, #1549, #1550, #1555, #1557, #1558, #1559, #1564, #1565, #1568, #1570,
  #1572, #1573, #1577, #1579, #1580, #1583, #1585, #1586, #1592, #1600, #1601,
  and #1602.

# 3.0.0 -- 2023-06-26

## Language changes

* Cryptol now includes a redesigned module system that is significantly more
  expressive than in previous releases. The new module system includes the
  following features:

  * Nested modules: Modules may now be defined within other modules.

  * Named interfaces: An interface specifies the parameters to a module.
    Separating the interface from the parameter declarations makes it possible
    to have different parameters that use the same interface.

  * Top-level module constraints: These are useful to specify constraints
    between different module parameters (i.e., ones that come from different
    interfaces or multiple copies of the same interface).

  See the
  [manual section](https://galoisinc.github.io/cryptol/master/Modules.html#instantiation-by-parametrizing-declarations)
  for more information.

* Declarations may now use *numeric constraint guards*.   This is a feature
  that allows a function to behave differently depending on its numeric
  type parameters.  See this [manual section](https://galoisinc.github.io/cryptol/master/BasicSyntax.html#numeric-constraint-guards)
  for more information.

* The foreign function interface (FFI) has been added, which allows Cryptol to
  call functions written in C. See this [manual section](https://galoisinc.github.io/cryptol/master/FFI.html)
  for more information.

* The unary `-` operator now has the same precedence as binary `-`, meaning
  expressions like `-x^^2` will now parse as `-(x^^2)` instead of `(-x)^^2`.
  **This is a breaking change.** A warning has been added in cases where the
  behavior has changed, and can be disabled with `:set warnPrefixAssoc=off`.

* Infix operators are now allowed in import lists: `import M ((<+>))` will
  import only the operator `<+>` from module `M`.

* `lib/Array.cry` now contains an `arrayEq` primitive. Like the other
  array-related primitives, this has no computational interpretation (and
  therefore cannot be used in the Cryptol interpreter), but it is useful for
  stating specifications that are used in SAW.

## New features

* Add a `:time` command to benchmark the evaluation time of expressions.

* Add support for literate Cryptol using reStructuredText.  Cryptol code
  is extracted from `.. code-block:: cryptol` and `.. sourcecode:: cryptol`
  directives.

* Add a syntax highlight file for Vim,
  available in `syntax-highlight/cryptol.vim`

* Add `:new-seed` and `:set-seed` commands to the REPL.
  These affect random test generation,
  and help write reproducable Cryptol scripts.

* Add support for the CVC5 solver, which can be selected with
  `:set prover=cvc5`. If you want to specify a What4 or SBV backend, you can
  use `:set prover=w4-cvc5` or `:set prover=sbv-cvc5`, respectively. (Note that
  `sbv-cvc5` is non-functional on Windows at this time due to a downstream issue
  with CVC5 1.0.4 and earlier.)

* Add `:file-deps` commands to the REPL and Python API.
  It shows information about the source files and dependencies of
  modules or Cryptol files.

## Bug fixes

* Fix a bug in the What4 backend that could cause applications of `(@)` with
  symbolic `Integer` indices to become out of bounds (#1359).

* Fix a bug that caused finite bitvector enumerations to panic when used in
  combination with `(#)` (e.g., `[0..1] # 0`).

* Cryptol's markdown parser is slightly more permissive and will now parse code
  blocks with whitespace in between the backticks and `cryptol`. This sort of
  whitespace is often inserted by markdown generation tools such as `pandoc`.

* Improve documentation for `fromInteger` (#1465)

* Closed issues #812, #977, #1090, #1140, #1147, #1253, #1322, #1324, #1329,
  #1344, #1347, #1351, #1354, #1355, #1359, #1366, #1368, #1370, #1371, #1372,
  #1373, #1378, #1383, #1385, #1386, #1391, #1394, #1395, #1396, #1398, #1399,
  #1404, #1415, #1423, #1435, #1439, #1440, #1441, #1442, #1444, #1445, #1448,
  #1449, #1450, #1451, #1452, #1456, #1457, #1458, #1462, #1465, #1466, #1470,
  #1475, #1480, #1483, #1484, #1485, #1487, #1488, #1491, #1496, #1497, #1501,
  #1503, #1510, #1511, #1513, and #1514.

* Merged pull requests #1184, #1205, #1279, #1356, #1357, #1358, #1361, #1363,
  #1365, #1367, #1376, #1379, #1380, #1384, #1387, #1388, #1393, #1401, #1402,
  #1403, #1406, #1408, #1409, #1410, #1411, #1412, #1413, #1414, #1416, #1417,
  #1418, #1419, #1420, #1422, #1424, #1429, #1430, #1431, #1432, #1436, #1438,
  #1443, #1447, #1453, #1454, #1459, #1460, #1461, #1463, #1464, #1467, #1468,
  #1472, #1473, #1474, #1476, #1477, #1478, #1481, #1493, #1499, #1502, #1504,
  #1506, #1509, #1512, #1516, #1518, #1519, #1520, #1521, #1523, #1527, and
  #1528.

# 2.13.0

## Language changes

* Update the implementation of the Prelude function `sortBy` to use
  a merge sort instead of an insertion sort. This improves the both
  asymptotic and observed performance on sorting tasks.

## UI improvements

* "Type mismatch" errors now show a context giving more information
  about the location of the error.   The context is shown when the
  part of the types match, but then some nested types do not.
  For example, when mathching `{ a : [8], b : [8] }` with
  `{ a : [8], b : [16] }` the error will be `8` does not match `16`
  and the context will be `{ b : [ERROR] _ }` indicating that the
  error is in the length of the sequence of field `b`.

## Bug fixes

* The What4 backend now properly supports Boolector 3.2.2 or later.

* Make error message locations more precise in some cases (issue #1299).

* Make `:reload` behave as expected after loading a module with `:module`
  (issue #1313).

* Make `include` paths work as expected when nested within another `include`
  (issue #1321).

* Fix a panic that occurred when loading dependencies before `include`s are
  resolved (issue #1330).

* Closed issues #1098, #1280, and #1347.

* Merged pull requests #1233, #1300, #1301, #1302, #1303, #1305, #1306, #1307,
  #1308, #1311, #1312, #1317, #1319, #1323, #1326, #1331, #1333, #1336, #1337,
  #1338, #1342, #1346, #1348, and #1349.

# 2.12.0

## Language changes
* Updates to the layout rule.  We simplified the specification and made
  some minor changes, in particular:
    - Paren blocks nested in a layout block need to respect the indentation
      if the layout block
    - We allow nested layout blocks to have the same indentation, which is
      convenient when writing `private` declarations as they don't need to
      be indented as long as they are at the end of the file.

* New enumeration forms `[x .. y by n]`, `[x .. <y by n]`,
  `[x .. y down by n]` and `[x .. >y down by n]` have been
  implemented. These new forms let the user explicitly specify
  the stride for an enumeration, as opposed to the previous
  `[x, y .. z]` form (where the stride was computed from `x` and `y`).

* Nested modules are now available (from pull request #1048). For example, the following is now valid Cryptol:

        module SubmodTest where

        import submodule B as C

        submodule A where
          propA = C::y > 5

        submodule B where
          y : Integer
          y = 42

## New features

* What4 prover backends now feature an improved multi-SAT procedure
  which is significantly faster than the old algorithm. Thanks to
  Levent Erkök for the suggestion.

* There is a new `w4-abc` solver option, which communicates to ABC
  as an external process via What4.

* Expanded support for declaration forms in the REPL. You can now
  define infix operators, type synonyms and mutually-recursive functions,
  and state signatures and fixity declarations. Multiple declarations
  can be combined into a single line by separating them with `;`,
  which is necessary for stating a signature together with a
  definition, etc.

* There is a new `:set path` REPL option that provides an alternative to
  `CRYPTOLPATH` for controlling where to search for imported modules
  (issue #631).

* The `cryptol-remote-api` server now natively supports HTTPS (issue
  #1008), `newtype` values (issue #1033), and safety checking (issue
  #1166).

* Releases optionally include solvers (issue #1111). See the
  `*-with-solvers*` files in the assets list for this release.

## Bug fixes

* Closed issues #422, #436, #619, #631, #633, #640, #680, #734, #735,
  #759, #760, #764, #849, #996, #1000, #1008, #1019, #1032, #1033,
  #1034, #1043, #1047, #1060, #1064, #1083, #1084, #1087, #1102, #1111,
  #1113, #1117, #1125, #1133, #1142, #1144, #1145, #1146, #1157, #1160,
  #1163, #1166, #1169, #1175, #1179, #1182, #1190, #1191, #1196, #1197,
  #1204, #1209, #1210, #1213, #1216, #1223, #1226, #1238, #1239, #1240,
  #1241, #1250, #1256, #1259, #1261, #1266, #1274, #1275, #1283, and
  #1291.

* Merged pull requests #1048, #1128, #1129, #1130, #1131, #1135, #1136,
  #1137, #1139, #1148, #1149, #1150, #1152, #1154, #1156, #1158, #1159,
  #1161, #1164, #1165, #1168, #1170, #1171, #1172, #1173, #1174, #1176,
  #1181, #1183, #1186, #1188, #1192, #1193, #1194, #1195, #1199, #1200,
  #1202, #1203, #1205, #1207, #1211, #1214, #1215, #1218, #1219, #1221,
  #1224, #1225, #1227, #1228, #1230, #1231, #1232, #1234, #1242, #1243,
  #1244, #1245, #1246, #1247, #1248, #1251, #1252, #1254, #1255, #1258,
  #1263, #1265, #1268, #1269, #1270, #1271, #1272, #1273, #1276, #1281,
  #1282, #1284, #1285, #1286, #1287, #1288, #1293, #1294, and #1295.

# 2.11.0

## Language changes

* The `newtype` construct, which has existed in the interpreter in an
  incomplete and undocumented form for quite a while, is now fullly
  supported. The construct is documented in section 1.22 of [Programming
  Cryptol](https://cryptol.net/files/ProgrammingCryptol.pdf). Note,
  however, that the `cryptol-remote-api` RPC server currently does not
  include full support for referring to `newtype` names, though it can
  work with implementations that use `newtype` internally.

## New features

* By default, the interpreter will now track source locations of
  expressions being evaluated, and retain call stack information.
  This information is incorporated into error messages arising from
  runtime errors. This additional bookkeeping incurs significant
  runtime overhead, but may be disabled using the `--no-call-stacks`
  command-line option.

* The `:exhaust` command now works for floating-point types and the
  `:check` command now uses more representative sampling of
  floating-point input values to test.

* The `cryptol-remote-api` RPC server now has methods corresponding to
  the `:prove` and `:sat` commands in the REPL.

* The `cryptol-eval-server` executable is a new, stateless server
  providing a subset of the functionality of `cryptol-remote-api`
  dedicated entirely to invoking Cryptol functions on concrete inputs.

## Internal changes

* A single running instance of the SMT solver used for type checking
  (Z3) is now used to check a larger number of type correctness queries.
  This means that fewer solver instances are invoked, and type checking
  should generally be faster.

* The Cryptol interpreter now builds against `libBF` version 0.6, which
  fixes a few bugs in the evaluation of floating-point operations.

## Bug fixes

* Closed issues #118, #398, #426, #470, #491, #567, #594, #639, #656,
  #698, #743, #810, #858, #870, #905, #915, #917, #962, #973, #975,
  #980, #984, #986, #990, #996, #997, #1002, #1006, #1009, #1012, #1024,
  #1030, #1035, #1036, #1039, #1040, #1044, #1045, #1049, #1050, #1051,
  #1052, #1063, #1092, #1093, #1094, and #1100.

# 2.10.0

## Language changes

* Cryptol now supports primality checking at the type level. The
  type-level predicate `prime` is true when its parameter passes the
  Miller-Rabin probabilistic primality test implemented in the GMP
  library.

* The `Z p` type is now a `Field` when `p` is prime, allowing additional
  operations on `Z p` values.

* The literals `0` and `1` can now be used at type `Bit`, as
  alternatives for `False` and `True`, respectively.

## New features

* The interpreter now includes a number of primitive functions that
  allow faster execution of a number of common cryptographic functions,
  including the core operations of AES and SHA-2, operations on GF(2)
  polynomials (the existing `pmod`, `pdiv`, and `pmult` functions), and
  some operations on prime field elliptic curves. These functions are
  useful for implementing higher-level algorithms, such as many
  post-quantum schemes, with more acceptable performance than possible
  when running a top-to-bottom Cryptol implementation in the
  interpreter.

  For a full list of the new primitives, see the new Cryptol
  [`SuiteB`](https://github.com/GaloisInc/cryptol/blob/master/lib/SuiteB.cry)
  and
  [`PrimeEC`](https://github.com/GaloisInc/cryptol/blob/master/lib/PrimeEC.cry)
  modules.

* The REPL now allows lines containing only comments, making it easier
  to copy and paste examples.

* The interpreter has generally improved performance overall.

* Several error messages are more comprehensible and less verbose.

* Cryptol releases and nightly builds now include an RPC server
  alongside the REPL. This provides an alternative interface to the same
  interpreter and proof engine available from the REPL, but is
  better-suited to programmatic use. Details on the protocol used by the
  server are available
  [here](https://github.com/GaloisInc/argo/blob/master/docs/Protocol.rst).
  A Python client for this protocol is available
  [here](https://github.com/GaloisInc/argo/tree/master/python).

* Windows builds are now distributed as both `.tar.gz` and `.msi` files.

## Bug Fixes

* Closed issues #98, #485, #713, #744, #746, #787, #796, #803, #818,
  #826, #838, #856, #873, #875, #876, #877, #879, #880, #881, #883,
  #886, #887, #888, #892, #894, #901, #910, #913, #924, #926, #931,
  #933, #937, #939, #946, #948, #953, #956, #958, and #969.

# 2.9.1

## Language changes

* The type of `generate` which is used for `a@i` sequence definitions,
   is generalized so that the index type can be any `Integral` type
   large enough to index the entire array being defined.

## Bug Fixes

* Closed issues #848, #850, #851, #859, and #861.

* Fixed Windows installer paths.

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

* Closed issues #346, #444, #614, #617, #636, #660, #662, #663, #664,
  #667, #670, #702, #711, #712, #716, #723, #725, #731, #835, #836,
  #839, #840, and #845

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

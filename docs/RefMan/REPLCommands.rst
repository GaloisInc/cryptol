REPL Commands
=============

Commands
--------
``:! COMMAND``
    Execute a command in the shell

``:? TOPIC``, ``:help TOPIC``
    Display a brief description of a function, type, or command. (e.g. :help
    :help)

    TOPIC can be any of:
      * Specific REPL colon-commands (e.g. ``:help :prove``)
      * Functions (e.g. ``:help join``)
      * Infix operators (e.g. ``:help +``)
      * Type constructors (e.g. ``:help Z``)
      * Type constraints (e.g. ``:help fin``)
      * ``:set``-able options (e.g. ``:help :set base``)

``:ast EXPR``
    Print out the pre-typechecked AST of a given term.

``:b MODULE``, ``:browse MODULE``
    Display information about loaded modules.

    With no argument, ``:browse`` shows information about the names in scope.
    With an argument ``M``, shows information about the names exported from 
    ``M``.

``:cd DIR``
    Set the current working directory.

``:check [EXPR]``
    Use random testing to check that the argument always returns true. (If no 
    argument, check all properties.)

    By default, this will check up to 100 test cases, or until the possible
    inputs are exhausted. This value can be changed with 
    ``:set tests=[NEW VAL]``.

``:debug_specialize EXPR``
    Do type specialization on a closed expression.

``:dumptests FILE EXPR``
    Dump a tab-separated collection of tests for the given expression into a
    file. The first column in each line is the expected output, and the
    remainder are the inputs. The number of tests is determined by the ``tests``
    option.

``:e FILE``, ``:edit FILE``
    Edit FILE or the currenly loaded module.

``:eval EXPR``
    Evaluate an expression with the reference evaluator.

``:exhaust [EXPR]``
    Use exhaustive testing to prove that the argument always returns true. (If
    no argument, check all properties.)

``:extract-coq``
    Print out the post-typechecked AST of all currently defined terms, in a Coq-
    parseable format.

``:file-deps FILE``
    Show information about the dependencies of a file.

``:generate-foreign-header FILE``
    Generate a C header file from foreign declarations in a Cryptol file.

    Converts all foreign declarations in the given Cryptol file into C function
    declarations, and writes them to a file with the same name but with a ``.h``
    extension.

``:l FILE``, ``:load FILE``
    Load a module by filename.

``:m [MODULE]``, ``:module [MODULE]``
    Load a module by its name.

``:module-deps MODULE``
    Show information about the dependencies of a module.

``:new-seed``
    Randomly generate and set a new seed for the random number generator.

``:prove [EXPR]``
    Use an external solver to prove that the argument always returns true. (If
    no argument, check all properties.)

    If the expression is successfully proven, the screen will display ``Q.E.D``.
    If not, the screen will display a counterexample that returns false.

``:q``, ``:quit``
    Exit the REPL.

``:r``, ``:reload``
    Reload the currently loaded module.

``:readByteArray FILE``
    Read data from a file as type ``fin n => [n][8]``, binding the value to
    variable ``it``.

``:s [OPTION=[VALUE]]``, ``:set [OPTION=[VALUE]]``
    Set an environmental option (``:set`` on its own displays current values).

``:safe [EXPR]``
    Uses an external solver to prove that an expression is safe (does not
    encounter run-time errors) for all inputs.

``:sat [EXPR]``
    Uses a solver to find a satisfying assignment for which the argument returns
    true. (If no argument, find an assignment for all properties.)

    By default, this will return one assignment, but that can be updated with
    ``:set satNum=VAL``

``:set-seed SEED``
    Seed the random number generator for operations using randomness.

    A seed takes the form of either a single integer or a 4-tuple of unsigned
    64-bit integers. Examples of commands using randomness are ``:dumpTests``
    and ``:check``.

``:t EXPR``, ``:type EXPR``
    Check the type of an expression.

``:time EXPR``
    Measure the time it takes to evaluate the given expression.

    The expression will be evaluated many times to get accurate results. Note
    that the first evaluation of a binding may take longer due to laziness, and
    this may affect the reported time. If this is not desired then make sure to
    evaluate the expression once first before running ``:time``. 

    The amount of time to spend collecting measurements can be changed with the
    ``timeMeasurementPeriod`` option. 

    Reports the average wall clock time, CPU time, and cycles. (Cycles are in
    unspecified units that may be CPU cycles.)

    Binds the result to

    .. code-block:: cryptol

        it : { avgTime : Float64
                , avgCpuTime : Float64
                , avgCycles : Integer }

``:version``
    Displays the version of the Cryptol executable.

``:w FILE EXPR``, ``:writeByteArray FILE EXPR``
    Write data of type ``fin n => [n][8]`` to a file.

:set Options
------------

``:set base``
    **Default value:** ``16``

    **Valid values:** ``2``, ``8``, ``10``, ``16``

    The base to display words at

``:set debug``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Enable debugging output

``:set ascii``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Whether to display 7- or 8-bit words using ASCII notation

``:set infLength``
    **Default value:** ``5``
    
    **Valid values:** any positive integer

    The number of elements to display for infinite sequences

``:set tests``
    **Default value:** ``100``
    
    **Valid values:** any positive integer

    The number of random tests to try with ``:check``

``:set satNum``
    **Default value:** ``1``

    **Valid values:** any positive integer, ``all``

    The maximum number of ``:sat`` solutions to display ("all" for no limits)

``:set prover``
    **Default value:** ``z3``

    **Valid values:** ``cvc4``, ``cvc5``, ``yices``, ``z3``, ``boolector``,
    ``mathsat``, ``abc``, ``bitwuzla``, ``offline``, ``any``, ``sbv-cvc4``,
    ``sbv-cvc5``, ``sbv-yices``, ``sbv-z3``, ``sbv-boolector``, ``sbv-mathsat``,
    ``sbv-abc``, ``sbv-bitwuzla``, ``sbv-offline``, ``sbv-any``, ``w4-cvc4``,
    ``w4-cvc5``, ``w4-yices``, ``w4-z3``, ``w4-boolector``, ``w4-abc``,
    ``w4-bitwuzla``, ``w4-offline``, ``w4-any``

    The external SMT solver for ``:prove`` and ``:sat``

``:set warnDefaulting``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Choose whether to display warnings when defaulting

``:set warnShadowing``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Choose whether to display warnings when shadowing symbols

``:set warnPrefixAssoc``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Choose whether to display warnings when expression association has changed 
    due to new prefix operator fixities

``:set warnUninterp``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Choose whether to issue a warning when uninterpreted functions are used to 
    implement primitives in the symbolic simulator

``:set warnNonExhaustiveConstraintGuards``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Choose whether to issue a warning when a use of constraint guards is not
    determined to be exhaustive

``:set smtFile``
    **Default value:** ``-``

    **Valid values:** Any file path, ``-``

    The file to use for SMT-Lib scripts (for debugging or offline proving). Use
    ``-`` for stdout

``:set path``
    **Default value:**

    **Valid values:** Any file path, empty

    The search path for finding named Cryptol modules

``:set monoBinds``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Whether or not to generalize bindings in a ``where`` clause

``:set tcSolver``
    **Default value:** ``z3 -smt2 -in``

    **Valid values:** a valid executable

    The solver that will be used by the type checker

``:set tcDebug``
    **Default value:** ``0``

    **Valid values:** ``0``, any positive integer

    Enable type-checker debugging output:
        * ``0`` no debug output
        * ``1`` show type-checker debug info
        * ``>1`` show type-checker debug info and interactions with SMT solver

``:set coreLint``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Enable sanity checking of type-checker

``:set hashConsing``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``
    
    Enable hash-consing in the What4 symbolic backends

``:set proverStats``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Enable prover timing statistics

``:set proverValidate``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Validate ``:sat`` examples and ``:prove`` counter-examples for correctness

``:set showExamples``
    **Default value:** ``on``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Print the (counter) examples after ``:sat`` or ``:prove``

``:set fpBase``
    **Default value:** ``16``

    **Valid values:** ``2``, ``8``, ``10``, ``16``

    The base to display floating point numbers at

``:set fpFormat``
    **Default value:** ``free``

    **Valid values:** ``free``, ``free+exp``, ``.NUM``, ``NUM``, ``NUM+exp``

    Specifies the format to use when displaying floating point numbers:
        * ``free``      show using as many digits as needed
        * ``free+exp``  like ``free`` but always show exponent
        * ``.NUM``      show NUM (>=1) digits after floating point
        * ``NUM``       show using NUM (>=1) significant digits
        * ``NUM+exp``   like NUM but always show exponent

``:set ignoreSafety``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Ignore safety predicates when performing ``:sat`` or ``:prove`` checks

``:set fieldOrder``
    **Default value:** ``display``

    **Valid values:** ``display``, ``canonical``

    The order that record fields are displayed in
        * ``display`` try to match the order they were written in the source code
        * ``canonical`` use a predictable, canonical order

``:set timeMeasurementPeriod``
    **Default value:** ``10``

    **Valid values:** any positive integer

    The period of time in seconds to spend collecting measurements when running
    ``:time``.
    
    This is a lower bound and the actual time taken may be higher if the
    evaluation takes a long time.

``:set timeQuiet``
    **Default value:** ``off``

    **Valid values:** ``off``, ``on``, ``false``, ``true``

    Suppress output of ``:time`` command and only bind result to ``it``


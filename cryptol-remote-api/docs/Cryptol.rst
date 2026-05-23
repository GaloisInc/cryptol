Cryptol RPC Server
==================

Fundamental Protocol
--------------------

This application is a `JSON-RPC <https://www.jsonrpc.org/specification>`_ server. Additionally, it maintains a persistent cache of application states and explicitly indicates the state in which each command is to be carried out.

Transport
~~~~~~~~~

The server supports three transport methods:


``stdio``
  in which the server communicates over ``stdin`` and ``stdout`` using `netstrings. <http://cr.yp.to/proto/netstrings.txt>`_
  
  

``socket``
  in which the server communicates over a socket using `netstrings. <http://cr.yp.to/proto/netstrings.txt>`_
  
  

``http``
  in which the server communicates over a socket using HTTP.
  
  

Application State
~~~~~~~~~~~~~~~~~

According to the JSON-RPC specification, the ``params`` field in a message object must be an array or object. In this protocol, it is always an object. While each message may specify its own arguments, every message has a parameter field named ``state``.

When the first message is sent from the client to the server, the ``state`` parameter should be initialized to the JSON null value ``null``. Replies from the server may contain a new state that should be used in subsequent requests, so that state changes executed by the request are visible.

In particular, per JSON-RPC, non-error replies are always a JSON object that contains a ``result`` field. The result field always contains an ``answer`` field and a ``state`` field, as well as ``stdout`` and ``stderr``.


``answer``
  The value returned as a response to the request (the precise contents depend on which request was sent).
  
  

``state``
  The state, to be sent in subsequent requests. If the server did not modify its state in response to the command, then this state may be the same as the one sent by the client. When a new state is in a server response, the previous state may no longer be available for requests.
  
  

``stdout`` and ``stderr``
  These fields contain the contents of the Unix ``stdout`` and ``stderr`` file descriptors. They are intended as a stopgap measure for clients who are still in the process of obtaining structured information from the libraries on which they depend, so that information is not completely lost to users. However, the server may or may not cache this information and resend it. Applications are encouraged to used structured data and send it deliberately as the answer.
  
  
The precise structure of states is considered an implementation detail that could change at any time. Please treat them as opaque tokens that may be saved and re-used within a given server process, but not created by the client directly.



Summary
-------

An RPC server for `Cryptol <https://https://cryptol.net/>`_ that supports type checking and evaluation of Cryptol code via the methods documented below.


Terms and Types
---------------

.. _Expression:
JSON Cryptol Expressions
~~~~~~~~~~~~~~~~~~~~~~~~

In the API, Cryptol expressions can be represented by the following:


JSON Booleans
  Represent the corresponding Cryptol Booleans
  
  

JSON Integers
  Cryptol integer literals, that can be used at a variety of types
  
  

JSON Strings
  Cryptol concrete syntax
  
  

JSON Objects
  Objects can represent a variety of Cryptol expressions. The field ``expression`` contains a tag that can be used to determine the remaining fields.
  
  
The tag values in objects can be:


``bits``
  
  * The expression is a bitvector. Further fields are:
    
    
  
  * ``encoding``: Either the string ``base64`` or ``hex``, for base-64 or hexadecimal representations of the bitvector
    
    
  
  * ``data``: A string containing the actual data
    
    
  
  * ``width``: An integer: the bit-width of the represented bit vector
    
    
  

``record``
  The expression is a record. The field ``data`` is a JSON object that maps record field names to :ref:`JSON Cryptol expressions <Expression>`.
  
  

``sequence``
  The expression is a sequence. The field ``data``contains a JSON array of the elements of the sequence; each is a JSON Cryptol expression.
  
  

``tuple``
  The expression is a tuple. The field ``data``contains a JSON array of the elements of the tuple; each is a JSON Cryptol expression.
  
  

``unit``
  The expression is the unit constructor, and there are no further fields.
  
  

``let``
  
  * The expression is a ``where``binding. The fields are:
    
    
  
  * 
    ``binders``
      
      * A list of binders. Each binder is an object with two fields:
        
        
      
      * ``name``: A string that is the name to be bound, and
        
        
      
      * ``definition``A :ref:`JSON Cryptol expression <Expression>`.
        
        
      
    
    ``body``
      A :ref:`JSON Cryptol expression <Expression>` in which the bound names may be used.
      
      
    
  

``call``
  
  * The expression is a function application. Further fields are:
    
    
  
  * ``function``: A :ref:`JSON Cryptol expression <Expression>`.
    
    
  
  * ``arguments``: A JSON array of :ref:`JSON Cryptol expressions <Expression>`.
    
    
  

``instantiate``
  
  * The expression is a type application. Further fields are:
    
    
  
  * ``generic``: The polymorphic expression to be instantiated
    
    
  
  * ``arguments``: A JSON object in which keys are the names of type parameters and values are :ref:`JSON Cryptol types <JSONSchema>`.
    
    
  

``integer modulo``
  
  * The expression is an integer with a modulus (the Cryptol ``Z`` type). Further fields are:
    
    
  
  * ``integer``: A JSON number, representing the integer
    
    
  
  * ``modulus``: A JSON number, representing the modulus
    
    
  

``variable``
  The expression is a variable bound by the server. The field ``identifier`` contains the name of the variable.
  
  

.. _JSONSchema:
JSON Cryptol Types
~~~~~~~~~~~~~~~~~~

JSON representations of types are type schemas. A type schema has three fields:


``forall``
  Contains an array of objects. Each object has two fields: ``name`` is the name of a type variable, and ``kind`` is its kind. There are four kind formers: the string ``Type`` represents ordinary datatypes, the string ``Num`` is the kind of numbers, and ``Prop`` is the kind of propositions. Arrow kinds are represented by objects in which the field ``kind`` is the string ``arrow``, and the fields ``from`` and ``to`` are the kinds on the left and right side of the arrow, respectively.
  
  

``propositions``
  A JSON array of the constraints in the type.
  
  

``type``
  The type in which the variables from ``forall`` are in scope and the constraints in ``propositions`` are in effect.
  
  

.. _DocstringResult:
DocstringResult
~~~~~~~~~~~~~~~

The result of evaluating the code fences in a docstring


``name``
  The definition assocated with the docstring
  
  

``fences``
  An array code fences each containing an array of individual :ref:`command results <CommandResult>`
  
  

.. _CommandResult:
CommandResult
~~~~~~~~~~~~~

The result of executing a single REPL command.


``success``
  Boolean indicating successful execution of the command
  
  

``type``
  The string representation of the type returned or null
  
  

``value``
  The string representation of the value returned or null
  
  

.. _ScanStatus:
ScanStatus
~~~~~~~~~~

List of module names and status of each.


``scanned``
  This file was successfully parsed and contains a change status.
  
  

``invalid_module``
  This file could not be parsed an analyzed due to syntax issues.
  
  

``invalid_dep``
  This file depends on a module that was not able to be loaded.
  
  

.. _LoadProjectMode:
LoadProjectMode
~~~~~~~~~~~~~~~




``modified``
  Load modified files and files that depend on modified files
  
  

``untested``
  Load files that do not have a current test result
  
  

``unsuccessful``
  Load files that do not have a successful test result
  
  

``refresh``
  Reload all files in the project discarding the cache results
  
  


Methods
-------

version (command)
~~~~~~~~~~~~~~~~~

Version information about this Cryptol server.

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++


``RPC server version``
  The cryptol-remote-api version string.
  
  

``version``
  The Cryptol version string.
  
  

``commit hash``
  The string of the git commit hash during the build of Cryptol.
  
  

``commit branch``
  The string of the git commit branch during the build of Cryptol.
  
  

``commit dirty``
  True iff non-committed files were present during the build of Cryptol.
  
  

``FFI enabled``
  True iff the FFI is enabled.
  
  


check (command)
~~~~~~~~~~~~~~~

Tests a property against random values to give quick feedback.

Parameter fields
++++++++++++++++


``expression``
  The predicate (i.e., function) to check; must be a monomorphic function with return type Bit.
  
  

``number of tests``
  The number of random inputs to test the property with, or ``all`` to exhaustively check the property (defaults to ``100`` if not provided). If ``all`` is specified and the property's argument types are not sufficiently small, checking may take longer than you are willing to wait!
  
  

Return fields
+++++++++++++


``tests run``
  The number of tests that were successfully run.
  
  

``tests possible``
  The maximum number of possible tests.
  
  

``result``
  The overall test result, represented as one of three string values:``pass`` (all tests succeeded), ``fail`` (a test evaluated to ``False``), or``error`` (an exception was raised during evaluation).
  
  

``arguments``
  Only returned if the ``result`` is ``fail`` or ``error``. An array of JSON objects indicating the arguments passed to the property which triggered the failure or error. Each object has an ``expr`` field, which is an individual argument expression, and a ``type`` field, which is the type of the argument expression.
  
  

``error message``
  Only returned if the ``result`` is ``error``. A human-readable representation of the exception that was raised during evaluation.
  
  


clear state (notification)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Clear a particular state from the Cryptol server (making room for subsequent/unrelated states).

Parameter fields
++++++++++++++++


``state to clear``
  The state to clear from the server to make room for other unrelated states.
  
  

Return fields
+++++++++++++

No return fields



clear all states (notification)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Clear all states from the Cryptol server (making room for subsequent/unrelated states).

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++

No return fields



extend search path (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Extend the server's search path with the given paths.

Parameter fields
++++++++++++++++


``paths``
  The paths to add to the search path.
  
  

Return fields
+++++++++++++

No return fields



load module (command)
~~~~~~~~~~~~~~~~~~~~~

Load the specified module (by name).

Parameter fields
++++++++++++++++


``module name``
  Name of module to load.
  
  

Return fields
+++++++++++++

No return fields



load file (command)
~~~~~~~~~~~~~~~~~~~

Load the specified module (by file path).

Parameter fields
++++++++++++++++


``file``
  File path of the module to load.
  
  

Return fields
+++++++++++++

No return fields



file-deps (command)
~~~~~~~~~~~~~~~~~~~

Get information about the dependencies of a file or module. The dependencies include the dependencies of modules nested in this one.

Parameter fields
++++++++++++++++


``name``
  Get information about this entity.
  
  

``is-file``
  Indicates if the name is a file (true) or module (false)
  
  

Return fields
+++++++++++++


``source``
  File containing the module. For internal modules this is an object { internal: "LABEL" }.
  
  

``fingerprint``
  A hash of the module content.
  
  

``includes``
  Files included in this module.
  
  

``imports``
  Modules imported by this module.
  
  

``foreign``
  Foreign libraries loaded by this module.
  
  


focused module (command)
~~~~~~~~~~~~~~~~~~~~~~~~

The 'current' module. Used to decide how to print names, for example.

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++


``module``
  The name of the focused module, which would be shown in the prompt in the Cryptol REPL, or ``null`` if there is no such focused module.
  
  

``parameterized``
  A Boolean value indicating whether the focused module is parameterized. This field is only present when the module name is not ``null``.
  
  


focus module (command)
~~~~~~~~~~~~~~~~~~~~~~

Focus the specified module (by name).

Parameter fields
++++++++++++++++


``module name``
  Name of module to focus.
  
  

Return fields
+++++++++++++

No return fields



evaluate expression (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Evaluate the Cryptol expression to a value.

Parameter fields
++++++++++++++++


``expression``
  The expression to evaluate.
  
  

Return fields
+++++++++++++


``value``
  A :ref:`JSON Cryptol expression <Expression>` that denotes the value
  
  

``type``
   A:ref:`JSON Cryptol type <JSONSchema>` that denotes the result type
  
  

``type string``
  A human-readable representation of the result type
  
  


call (command)
~~~~~~~~~~~~~~

Evaluate the result of calling a Cryptol function on one or more parameters.

Parameter fields
++++++++++++++++


``function``
  The function being called.
  
  

``arguments``
  The arguments the function is being applied to.
  
  

Return fields
+++++++++++++


``value``
  A :ref:`JSON Cryptol expression <Expression>` that denotes the value
  
  

``type``
   A:ref:`JSON Cryptol type <JSONSchema>` that denotes the result type
  
  

``type string``
  A human-readable representation of the result type
  
  


visible names (command)
~~~~~~~~~~~~~~~~~~~~~~~

List the currently visible (i.e., in scope) term names.

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++


``name``
  A human-readable representation of the name
  
  

``type string``
  A human-readable representation of the name's type schema
  
  

``type``
   A:ref:`JSON Cryptol type <JSONSchema>`
  
  

``module``
  A human-readable representation of the module from which the name originates
  
  

``parameter``
  An optional field which is present iff the name is a module parameter
  
  

``infix``
  An optional field which is present iff the name is an infix operator. If present, it contains an object with two fields. One field is ``associativity``, containing one of the strings ``left-associative``, ``right-associative``, or ``non-associative``, and the other is ``level``, containing the name's precedence level.
  
  

``pragmas``
  An optional field containing a list of the name's pragmas (e.g. ``property``), if it has any
  
  

``documentation``
  An optional field containing documentation string for the name, if it is documented
  
  


visible modules (command)
~~~~~~~~~~~~~~~~~~~~~~~~~

List the currently visible (i.e., in scope) module names.

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++


``module``
  A human-readable representation of the module's name
  
  

``documentation``
  An optional field containing documentation strings for the module, if it is documented
  
  

``parameterized``
  A Boolean value indicating whether the focused module is parameterized
  
  


check type (command)
~~~~~~~~~~~~~~~~~~~~

Check and return the type of the given expression.

Parameter fields
++++++++++++++++


``expression``
  Expression to type check.
  
  

Return fields
+++++++++++++


``type schema``
  A :ref:`JSON Cryptol Type <JSONSchema>`
  
  


prove or satisfy (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Find a value which satisfies the given predicate, or show that it is valid.(i.e., find a value which when passed as the argument produces true or show that for all possible arguments the predicate will produce true).

Parameter fields
++++++++++++++++


``prover``
  The SMT solver to use to check for satisfiability. I.e., one of the following: ``w4-cvc5``, ``w4-yices``, ``w4-z3``, ``w4-bitwuzla``, ``w4-boolector``, ``w4-abc``, ``w4-rme``, ``w4-offline``, ``w4-any``, ``cvc5``, ``yices``, ``z3``, ``bitwuzla``, ``boolector``, ``mathsat``, ``abc``, ``offline``, ``any``, ``sbv-cvc5``, ``sbv-yices``, ``sbv-z3``, ``sbv-bitwuzla``, ``sbv-boolector``, ``sbv-mathsat``, ``sbv-abc``, ``sbv-offline``, ``sbv-any``.
  
  

``expression``
  The function to check for validity, satisfiability, or safety depending on the specified value for ``query type``. For validity and satisfiability checks, the function must be a predicate (i.e., monomorphic function with return type Bit).
  
  

``result count``
  How many satisfying results to search for; either a positive integer or ``all``. Only affects satisfiability checks.
  
  

``query type``
  Whether to attempt to prove the predicate is true for all possible inputs (``prove``), find some inputs which make the predicate true (``sat``), or prove a function is safe (``safe``).
  
  

``hash consing``
  Whether or not to use hash consing of terms (if available).``true`` to enable or ``false`` to disable.
  
  

Return fields
+++++++++++++


``result``
  Either a string indicating the result of checking for validity, satisfiability, or safety---i.e., one of ``unsatisfiable``, ``invalid``, or ``satisfied``---or the string literal ``offline`` indicating an offline solver option was selected and the contents of the SMT query will be returned instead of a SAT result.
  
  

``counterexample type``
  Only used if the ``result`` is ``invalid``. This describes the variety of counterexample that was produced. This can be either ``safety violation`` or ``predicate falsified``.
  
  

``counterexample``
  Only used if the ``result`` is ``invalid``. A list of objects where each object has an ``expr``field, indicating a counterexample expression, and a ``type``field, indicating the type of the expression.
  
  

``models``
  Only used if the ``result`` is ``satisfied``. A list of list of objects where each object has an ``expr``field, indicating a expression in a model, and a ``type``field, indicating the type of the expression.
  
  

``query``
  Only used if the ``result`` is ``offline``. The raw textual contents of the requested SMT query which can inspected or manually given to an SMT solver.
  
  


check docstrings (command)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Check docstrings

Parameter fields
++++++++++++++++


``cache_id``
  A ``string`` identifying the cache state before validation.
  
  

Return fields
+++++++++++++


``results``
  A list of :ref:`docstring results <DocstringResult>` correspoding to each definition in the current module.
  
  

``cache_id``
  A ``string`` identifying the cache state after validation.
  
  


load project (command)
~~~~~~~~~~~~~~~~~~~~~~

Load project returning a list of all the modules and whether they have changed since the last load

Parameter fields
++++++++++++++++


``path``
  Path to directory containing the project
  
  

``mode``
  One of the modes described at :ref:`LoadProjectMode <LoadProjectMode>`.
  
  

Return fields
+++++++++++++


``scan_status``
  List of module name and :ref:` scan status <ScanStatus>`.
  
  

``test_results``
  List of module name and cached test result.
  
  


interrupt (notification)
~~~~~~~~~~~~~~~~~~~~~~~~

Interrupt the server, terminating it's current task (if one exists).

Parameter fields
++++++++++++++++

No parameters


Return fields
+++++++++++++

No return fields







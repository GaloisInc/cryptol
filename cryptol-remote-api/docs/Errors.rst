Errors returned by the JSON-RPC API
===================================

The JSON-RPC spec reserves the following error codes:

+ ``-32602``: “Invalid params” (for this particular known method)
+ ``-32700``: “Parse error” (i.e. invalid JSON)
+ ``-32601``: “Method not found”
+ ``-32600``: “Invalid request”
+ ``-32603``: “Internal error”

In the case where an error is returned and a ``data`` object is attached, it
MUST be a JSON object. It MAY contain a ``path`` field which, if present, MUST
be a string referencing a specific file to which the error pertains. It MAY also
contain a ``warnings`` field which, if present, MUST be a JSON list of warnings
which occurred alongside this error.

Specific errors are free to define all other fields of the ``data`` object to
hold data of their choice specific to the error at hand. In the lists of errors
below, informal JSON schemata will be used to describe the format of these
additional fields, omitting the mention of the ``path`` and ``warnings`` fields.
A client SHOULD expect that these fields may be present or absent from the
error response to any given request to the API.

Errors in the Argo Protocol Layer (``1``–``9999``)
--------------------------------------------------

If the client is correctly following the JSON-RPC spec but failing to conform to
the protocol of the state-caching Argo service, some errors may be thrown
specific to that.

State field (``1``–``99``)
~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``10``: “Missing state field”
-  ``20``: “Invalid state field” ``{ state: <JSON>, error: String }``

.. _saw-server-errors:

SAW Server Errors (``10000``–``19999``)
---------------------------------------

..
  The SAW server uses the same errors as the Cryptol server for Cryptol errors
  (that is, when a Cryptol error occurs it should be directly returned as such,
  which will have a code outside this range).

An error in this range should be considered a bug in a client: a client
correctly interacting with the Argo API should never see these errors, and they
are indicative that the client is doing something wrong.

Server value errors (``10000``–``10099``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``10000``: “No server value with name \____\_” ``{ name: String }``
- ``10010``: “The server value with name \____\_ is not a Cryptol environment”
   ``{ name: String }``
- ``10020``: “The server value with name \____\_ is not an LLVM module”
  ``{name: String }``
- ``10030``: “The server value with name \____\_ is not an LLVM setup script”
   ``{ name: String }``
- ``10040``: “The server value with name \____\_ is not an LLVM setup value”
   ``{ name: String }``
- ``10050``: “The server value with name \____\_ is not an LLVM method
   specification”
   ``{ name: String }``
- ``10080``: “The server value with name \____\_ is not a JVM class”
   ``{ name: String }``
- ``10090``: “The server value with name \____\_ is not a JVM method
   specification”
   ``{ name: String }``

Setup errors (``10100``–``10199``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``10100``: “Not currently setting up Cryptol”
-  ``10110``: “Not currently setting up Crucible/LLVM”
-  ``10120``: “Not at top level” ``{ tasks: [String] }``

Loading and filesystem errors (``10200``–``10299``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``10200``: “Can’t load LLVM module” ``{ error: String }``

Verification errors (``10300``–``19999``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``10300``: Verification exception ``{ error: String }``. This error will be
   likely split into several specific separate errors in the future and possibly
   deprecated.

Cryptol errors (``11000``, to be deprecated)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- ``11000``: Cryptol exception ``{ error: String }``. This error will be
  deprecated in a future release and Cryptol errors will instead be reported
  identically to the manner described below for the Cryptol-only server.

.. _cryptol-server-errors:

Cryptol Server Errors (``20000``–``29999``)
-------------------------------------------

Parse, print, and load errors (``20000``–``20199``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``20000``: “There was a Cryptol parse error”
   ``{ error: String, input: String }`` (the input is rendered as
   literal string)
-  ``20010``: “Bad UTF-8” ``{ path: String, error: String }``
-  ``20020``: “Invalid Base64” ``{ input: String }``
-  ``20030``: “Not a hex digit” ``{ input: String }``
-  ``20040``: “Can’t convert Cryptol data from this type to JSON”
   ``{ type: <JSON>, "type string": String }`` where the JSON object for ``type``
   is a :ref:`JSON Cryptol type <cryptol-json-type>`.
-  ``20050``: “Can’t find file” ``{ path: String }``
-  ``20051``: “Can’t find directory ``{ path: String }`` (this is for
   the ``ChangeDir`` method)
-  ``20060``: “Other IO error” ``{ path: String, error: String }``

Evaluation errors (``20200``–``20499``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``20200``: “Can’t evaluate at polymorphic type”
   ``{ type: <JSON>, "type string": String }`` where the JSON object for ``type``
   is a :ref:`JSON Cryptol type <cryptol-json-type>`.
-  ``20210``: “Execution would have required these defaults”
   ``{ defaults: [ { parameter: String, type: <JSON> "type string": String } ] }``
   where the JSON object for ``type`` is a
   :ref:`JSON Cryptol type <cryptol-json-type>`.
-  ``20220``: “Can’t evaluate Cryptol in a parameterized module”
   ``{ "type parameters": [String], "definitions": [String] }``
-  ``20230``: “Prover error” ``{ error: String }``

Module errors (``20500``–``20699``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``20500``: “Module not found” ``{ source: String, path: String }``
-  ``20540``: “Module parse error” ``{ source: String, error: String }``
-  ``20550``: “Recursive modules” ``{ modules: [String] }``
-  ``20600``: “Module name mismatch”
   ``{ expected: String, found: String }``
-  ``20610``: “Duplicate module name”
   ``{ name: String, paths: [String, String] (2-element list) }``
-  ``20630``: “Imported parameterized module” ``{ module: String }``
-  ``20640``: “Failed to parameterize module defs”
   ``{ module: String, parameters: [String] }``
-  ``20650``: “Not a parameterized module” ``{ module: String }``

Type errors (``20700``–``29999``)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  ``20700``: “Renamer error(s)”
   ``{ source: String, errors: [String] }``
-  ``20710``: “No pat errors” ``{ source: String, errors: [String] }``
-  ``20720``: “No include errors”
   ``{ source: String, errors: [String] }``
-  ``20730``: “Typechecking failed”
   ``{ source: String, errors: [String] }`` (could be split in future
   into many separate errors)
-  ``29999``: “Other failure” ``{ error: String }``

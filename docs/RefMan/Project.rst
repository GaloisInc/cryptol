Project Files
=============

Cryptol supports specifying a *project* file that can accelerate the
repeated loading and testing of a large, interconnected set of source
files. Cryptol will remember the hashes of the files previously checked
and use this to avoid type-checking and testing files that are unchanged
since the previous loading of the project.

To use this feature a ``cryproject.toml`` should be created in the root
directory of the cryptol source files that lists all of the top-level
modules of the project. The dependencies of these modules will implicitly
be added to the project.

To check a whole project, Cryptol can be invoked with the ``--project``
or ``-p`` flag using the directory containing the project as an
argument. This will type-check all of the modules in the project and
check the docstrings for all modules in the project.

All errors are reported to stdout. When all modules load and all tests
pass cryptol's exit code will be ``0``. When the project does not load
successfully the exit code is ``1``.

For each module, which is processed, we report a line like this:

.. code:: shell

  Successes: X, No fences: Y, Failures: Z

where:
  * ``X`` is the nubmer of docstring tests which completed successfully,
  * ``Y`` is the number of declarations that have no docstring tests, and
  * ``Z`` is the number of dcostring tests which resulted in an error.

Note that these are only reported for modules that are actually checked
(i.e., either they were not checked before, or something changed).

After all modules are processed we also report a summay of the form:

.. code:: shell

  Passing: X, Failing: Y, Missing: Z

where:
  * ``X`` is the number of modules that have no failing tests,
  * ``Y`` is the number of modules with at least one failing test, and
  * ``Z`` is the number of modules for which we did not run tests.

At present we do not run tests for built-in modules (e.g., ``Cryptol`` or
``Float``), so almost always there will be at least 1 "missing" module.

After loading a project the cache information is saved into a Cryptol-
managed file in the project root directory ``.cryproject/loadcache.toml``.

Example:

.. code:: shell

   cryptol -p myproject/

To discard the previous cached results and reload a whole project use
``--refresh-project``. This can be useful when versions of external
tools have changed or simply to get confidence that everything is still
in a working state.

Example:

.. code:: shell

   cryptol -p myproject/ --refresh-project


``cryproject.toml`` Format
--------------------------

Project files are described by a `TOML <https://toml.io/en/>`__ file
using the following top-level key-value assignments:

- ``root`` - *optional* - *string* - can optionally be specified to override the directory that
  Cryptol files are located in. Otherwise modules are loaded relative
  to the directory containing the ``cryproject.toml``.

- ``modules`` - *required* - *list of strings* -  is a list of filenames patterns matching the
  top-level modules in a project. These modules, and all of their dependencies, will be loaded
  when the project is loaded. These patterns will match using the common ``*``, ``?``, and
  character class matching of ``fnmatch`` extended with ``**`` matching for multiple directories
  as found in the Git format for ``.gitignore``

Example directory structure:

.. code::

   project
   ├── Id.c
   ├── Id.cry
   ├── Id.dylib
   ├── Main.cry
   └── cryproject.toml

Example ``cryproject.toml``:

.. code:: toml

   modules = [
       "Id.cry",
       "Main.cry",
   ]

``loadcache.toml`` Format
-------------------------

After loading a project a cache file is generated and stored in
``.cryproject/loadcache.toml``. This file contains a version number to
allow caches to automatically invalidate when the project subsystem
updates. Modules that fail to load at all are not listed in the cache
file and will be reprocessed on subsequent project loads even if unchanged.

- ``version`` - *integer* - specifies the cache file format version in order to allow
  old caches to be invalidated when Cryptol changes the meaning of this
  file.

- ``file`` - *string* - specifies the absolute path to a Cryptol module for those
  stored in files.

- ``memory`` - *string* - specifies the module name of a primitive module built into
  Cryptol.

- ``fingerprint`` - *string* - specifies a SHA2-256 hash of the source file which is
  used to detect when the source file has changed from the previous run.

- ``foreign_fingerprints`` - *list of string* - is a list of SHA2-256 hashes of dynamic
  libraries that this Cryptol file directly loads.

- ``include_fingerprints`` - *list of string* - is a list of SHA2-256 hashes of pre-processor
  included files that this Cryptol files directly includes.

- ``docstring_result`` - *boolean* - is ``true`` when ``:check-docstrings``
  previously succeeded for this module and ``false`` when it previously
  failed. It will be missing if tests were never run on this module.

.. code:: toml

   version = 1

   [[modules]]
   fingerprint = "2f671b21f2933a006b6a843c7f281388e6b8227f9944b111f87711dc9ca8448f"
   foreign_fingerprints = []
   include_fingerprints = []
   memory = "Cryptol"

   [[modules]]
   docstring_result = true
   file = "/path/to/project/Id.cry"
   fingerprint = "a9e6f7a4b65ead6bd8e27442717d6b0dc54afc73e34b18c32f005ceb7a8f3c34"
   foreign_fingerprints = [ "c7767a13281a56631c72b9b6f69a17746dc02213e7f2b24a8a4a6fe7afd9ee0a" ]
   include_fingerprints = []

   [[modules]]
   docstring_result = true
   file = "/path/to/project/Main.cry"
   fingerprint = "6b36f965ebb1a68cf76d689a966806ec879540aa6576a76c1aaa7705a4af09d5"
   foreign_fingerprints = []
   include_fingerprints = []

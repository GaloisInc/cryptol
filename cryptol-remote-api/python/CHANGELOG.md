# Revision history for `cryptol` Python package

## next

## 3.4.1 -- 2026-01-27

* Python 3.8, which is EOL, is no longer supported.

## 3.4.0 -- 2025-11-07

* The v3.4.0 release is made in tandem with the Cryptol 3.4.0 release. See the
  Cryptol 3.4.0 release notes for relevant Cryptol changes.

## 3.3.0 -- 2025-03-21

* Add `modules` command to return the modules, submodules and associated
  documentation for them.

* Add `focus module` command to set the current module for evaluation
  and running tests.

* Add `check docstrings` to run the docstring tests on the currently
  focused module.

## 3.2.1 -- 2024-08-18

* Require building with `argo-client-0.0.13` or later. `argo-client-0.0.13` uses
  blocking IO, which should reduce CPU load when receiving replies.

## 3.2.0 -- 2024-08-20

* The v3.2.0 release is made in tandem with the Cryptol 3.2.0 release. See the
  Cryptol 3.2.0 release notes for relevant Cryptol changes.

## 3.1.1 -- 2024-05-15

* Add support for Python 3.12.

## 3.1.0 -- 2024-02-05

* The v3.1.0 release is made in tandem with the Cryptol 3.1.0 release. See the
  Cryptol 3.1.0 release notes for relevant Cryptol changes.

## 3.0.1 -- 2023-07-10

* Update `cry_f` to property handle strings, length-0 `BV`s, and 1-tuples
* Add `version` command for fetching Cryptol/`cryptol-remote-api` version
  information

## 3.0.0 -- 2023-06-26

* The v3.0.0 release is made in tandem with the Cryptol 3.0.0 release. See the
  Cryptol 3.0.0 release notes for relevant Cryptol changes.
* Add `property_names` and `parameter_names` commands, used to get only those
  loaded names which are properties or module parameters, respectively.
* Add more fields (such as `pragmas`, `parameter`, `module`, and `infix`) to
  the result of `names` (see `cryptol-remote-api` `CHANGELOG`).
* Do not hang if `names` is called when a parameterized module is loaded
  (see `cryptol-remote-api` `CHANGELOG`).

## 2.13.0 -- 2022-05-17

* v2.13.0 release in tandem with the Cryptol 2.13.0 release. See the Cryptol
  2.13.0 release notes for relevant Cryptol changes. No notable changes to the
  RPC server or client since 2.12.4.

## 2.12.4 -- 2022-03-21

* fix: add `typing-extensions` as an explicit dependency for the client.

## 2.12.2 -- 2021-12-21

* Add an interface for Cryptol quasiquotation using an f-string-like syntax,
  see `tests/cryptol/test_quoting` for some examples.
* Fix a bug with the client's `W4_ABC` solver, add a `W4_ANY` solver.
* Deprecate `CryptolType.from_python` and `CryptolType.convert`
* Remove `CryptolType` arguments to `to_cryptol` and `__to_cryptol__`

## 2.12.0 -- 2021-11-19

* v2.12 release in tandem with Cryptol 2.12 release. See Cryptol release 2.12
  release notes for relevant Cryptol changes. No notable changes to RPC server
  or client since 2.11.7.

## 2.11.7 -- 2021-09-22

* Add a synchronous, type-annotated interface (`synchronous.py`). To use this
  interface, connect using `c = cryptol.sync.connect()` and remove all
  `.result()` calls.
* Add a single-connection, synchronous, type-annotated interface based on the
  above. To use this interface, add `from cryptol.single_connection import *`,
  connect using `connect()`, replace `c.eval(...).result()` with
  `cry_eval(...)`, remove all `c.` prefixes, and remove all `.result()` calls.
* Update most of the tests to use the single-connection interface.

## 2.11.6 -- 2021-09-10

* Add a `timeout` field to the `CryptolConnection` class which can be used
  to set a default timeout for all RPC interactions.
* Add an optional `timeout` keyword parameter to each `CryptolConnection` method
  which can specify a timeout for a particular method call.
* Add an `interrupt` method to the `CryptolConnection` class which interrupts
  any active requests on the server.

## 2.11.5 -- 2021-08-25

* From argo: Change the behavior of the `Command` `state` method so that after
  a `Command` raises an exception, subsequent interactions will not also raise
  the same exception.

## 2.11.4 -- 2021-07-22

* Add client logging option. See the `log_dest` keyword argument on
  `cryptol.connect` or the `logging` method on a `CryptolConnection` object.

## 2.11.3 -- 2021-07-20

* Removed automatic reset from `CryptolConnection.__del__`.


## 2.11.2 -- 2021-06-23

* Ability to leverage HTTPS/TLS while _disabling_ verification of SSL certificates.
  See the `verify` keyword argument on `cryptol.connection.connect(...)`.

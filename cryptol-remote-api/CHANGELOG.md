# Revision history for `cryptol-remote-api` and `cryptol-eval-server`

## 3.0.0 -- 2023-06-26

* The v3.0.0 release is made in tandem with the Cryptol 3.0.0 release. See the
  Cryptol 3.0.0 release notes for relevant Cryptol changes.
* Add more fields (such as `pragmas`, `parameter`, `module`, and `infix`) to
  the response to the RPC `visible names` method.
* Do not error if `visible names` is called when a parameterized module is
  loaded (this used to cause the appearance of the server hanging in such a
  case).

## 2.13.0 -- 2022-05-17

* v2.13.0 release in tandem with the Cryptol 2.13.0 release. See the Cryptol
  2.13.0 release notes for relevant Cryptol changes. No notable changes to the
  RPC server or client since 2.12.0.

## 2.12.0 -- 2021-11-19

* v2.12 release

## 2.11.1 -- 2021-06-23

* HTTPS/TLS support added. Enable by running server in `http` mode with `--tls`
  flag or by setting an environment variable (command line `--help` contains details).


## 2.11.0

* First "released" version of `cryptol-remote-api`.

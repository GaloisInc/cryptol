# Revision history for `cryptol` Python package

## 2.11.3 -- 2021-07-20

* Removed automatic reset from `CryptolConnection.__del__`.


## 2.11.2 -- 2021-06-23

* Ability to leverage HTTPS/TLS while _disabling_ verification of SSL certificates.
  See the `verify` keyword argument on `cryptol.connection.connect(...)`.

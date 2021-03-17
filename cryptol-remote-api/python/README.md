# Cryptol Python Package

In-development Python client for Cryptol's RPC server.

The Cryptol client depends on the [cryptol-remote-api](https://github.com/GaloisInc/cryptol/tree/master/cryptol-remote-api) server.

## Installation

To install the Python bindings, we recommend the use of a "virtual
environment" that isolates collections of Python packages that are
used for different projects. To create a virtual environment, use the
command:

```
$ python3 -m venv virtenv
```

The preferred mode of use for virtual environments is to *activate*
them, which modifies various environment variables to cause the
current shell's view of the Python implementations, tools, and
libraries to match the environment. For instance, `PATH` is modified
to prioritize the virtual environment's Python version, and that
Python is pointed at the specific collection of libraries that are
available. Under a broadly Bourne-compatible shell like `bash` or
`zsh`, source the appropriate file in the environment:

```
$ . virtenv/bin/activate
```

to activate the environment. Deactivate it using the shell alias
`deactivate` that is defined by `activate`. For other shells or
operating systems, please consult the documentation for `venv`. If
you prefer not to activate the environment, it is also possible to run
the environment's version of Python tooling by invoking the scripts in
its `bin` directory.

In the virtual environment, run the following command to install the
library's dependencies:

```
$ pip install -r requirements.txt
```

Next, install the library itself:

```
$ pip install -e .
```

The `-e` flag to `pip install` causes it to use the current files
in the repository as the library's source rather than copying them to
a central location in the virtual environment. This means that they
can be edited in-place and tested immediately, with no reinstallation
step. If you'd prefer to just install them, then omit the `-e` flag.

## Typechecking

To run the `mypy` type checker, enter the virtual environment and then run:

```
$ mypy cryptol tests
```

Actually using the application-specific bindings requires the
appropriate server (please refer to the links at the beginning of this
document).

## Testing

The unit tests for the standard RPC server and the eval-only RPC server can be run via the following commands respectively

```
$ python3 -m unittest discover tests/cryptol
$ python3 -m unittest discover tests/cryptol_eval
```

provided that either

1. the server binaries are visible from your `PATH`,
2. the `CRYPTOL_SERVER` environment variable points to an appropriate server binary when the test is run,  or
3. the `CRYPTOL_SERVER_URL` environment variable contains a URL which can be used to connect to a running instance of the appropriate server in HTTP mode (e.g., `http://localhost:8080/` if the server is being run locally and listening for connections on port `8080`).

